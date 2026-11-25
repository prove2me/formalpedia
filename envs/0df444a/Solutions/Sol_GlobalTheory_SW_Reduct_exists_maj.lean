-- Prove2me | solution 1 for GlobalTheory.SW.Reduct.exists_maj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:32.23083+00:00
-- url     : https://prove2.me/submissions/15475313-dd39-4dcb-aaf1-0b859dd1d96e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHigh
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Reduct
variable {N : ℕ}
namespace GlobalTheory.SW.Reduct
theorem _root_.solution {Z : Matrix (Fin N) (Fin N) ℂ} (hZ : (imH Z).PosDef) :
    let H := fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ) * (imH Z)⁻¹ * (fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ + I • Matrix.J (Fin N) ℂ
    H.PosDef ∧ H * (I • Matrix.J (Fin N) ℂ) * H = I • Matrix.J (Fin N) ℂ := by
  intro H
  set Y := imH Z with hY
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hZ.isUnit
  have h1 : Y * Y⁻¹ = 1 := mul_nonsing_inv _ hu
  have h2 : Y⁻¹ * Y = 1 := nonsing_inv_mul _ hu
  have hd : Z = Zᴴ + (2 * I) • Y := by
    rw [hY, imH, smul_smul, mul_inv_cancel₀ (by simp), one_smul]; abel
  have hJ : (I • Matrix.J (Fin N) ℂ) * (I • Matrix.J (Fin N) ℂ) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.J_squared]; simp
  have hP : (fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ * (I • Matrix.J (Fin N) ℂ) * fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ) = (-2 : ℂ) • Y := by
    rw [Matrix.mul_smul, Matrix.smul_mul, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.J, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
    simp only [Matrix.mul_zero, Matrix.mul_one, conjTranspose_one, zero_add, Matrix.one_mul,
      Matrix.mul_neg, add_zero]
    have : Z + -Zᴴ = (2 * I) • Y := by nth_rewrite 1 [hd]; abel
    rw [this, smul_smul]
    congr 1
    linear_combination 2 * I_mul_I
  have hH : H * (I • Matrix.J (Fin N) ℂ) * H = I • Matrix.J (Fin N) ℂ := by
    simp only [H]
    generalize I • Matrix.J (Fin N) ℂ = G at hJ hP ⊢
    generalize fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ) = P at hP ⊢
    have e : P * Y⁻¹ * Pᴴ * G * (P * Y⁻¹ * Pᴴ) = (-2 : ℂ) • (P * Y⁻¹ * Pᴴ) := by
      calc _ = P * Y⁻¹ * (Pᴴ * G * P) * Y⁻¹ * Pᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hP, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc P, h2,
            Matrix.mul_one]
    generalize P * Y⁻¹ * Pᴴ = K at e
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, e, Matrix.mul_assoc, hJ, Matrix.one_mul,
      Matrix.mul_one]
    module
  have hK : fromRows Zᴴ (1 : Matrix (Fin N) (Fin N) ℂ) * Y⁻¹ * (fromRows Zᴴ (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ =
      fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ) * Y⁻¹ * (fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ + (2 * I) • Matrix.J (Fin N) ℂ := by
    rw [conjTranspose_fromRows_eq_fromCols_conjTranspose,
      conjTranspose_fromRows_eq_fromCols_conjTranspose, fromRows_mul Zᴴ _ Y⁻¹, fromRows_mul Z _ Y⁻¹,
      fromRows_mul_fromCols, fromRows_mul_fromCols, Matrix.J, fromBlocks_smul, fromBlocks_add,
      conjTranspose_conjTranspose, conjTranspose_one]
    generalize Zᴴ = W at hd
    rw [hd]
    congr 1 <;>
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, h1, h2, smul_zero, add_zero, smul_neg, add_neg_cancel_right, ← Matrix.mul_assoc Y]
  have hS : H.PosSemidef := by
    have p1 := hZ.inv.posSemidef.mul_mul_conjTranspose_same (fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ))
    have p2 := hZ.inv.posSemidef.mul_mul_conjTranspose_same (fromRows Zᴴ (1 : Matrix (Fin N) (Fin N) ℂ))
    have p3 := (p1.add p2).smul (a := (2⁻¹ : ℂ)) (by positivity)
    rw [hK] at p3
    refine (congrArg Matrix.PosSemidef ?_).mp p3
    simp only [H]; module
  refine ⟨?_, hH⟩
  refine hS.posDef_iff_isUnit.2 ?_
  have : H * ((I • Matrix.J (Fin N) ℂ) * H * (I • Matrix.J (Fin N) ℂ)) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hH, hJ]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse this)
end GlobalTheory.SW.Reduct
