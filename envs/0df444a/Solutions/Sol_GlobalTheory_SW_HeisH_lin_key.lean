-- Prove2me | solution 1 for GlobalTheory.SW.HeisH.lin_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:15.02482+00:00
-- url     : https://prove2.me/submissions/0c1d98be-5dfc-480b-830b-cf553cdca3f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Theorems.Thm_P2M_GlobalTheory_SW_HAct_den__act_d7a6623b371e


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeisH
noncomputable section
variable {n N : ℕ}
namespace GlobalTheory.SW.HeisH
theorem _root_.solution {A B C D Z : Matrix (Fin N) (Fin N) ℂ} (P' Q' : Matrix (Fin n) (Fin N) ℂ)
    (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (h5 : C * Dᴴ = D * Cᴴ) (hQ : (C * Z + D).det ≠ 0) :
    ((P' * B + Q' * D) + (P' * A + Q' * C) * Z) * (C * Z + D)⁻¹ =
      Q' + P' * ((A * Z + B) * (C * Z + D)⁻¹) ∧
    (Z * Cᴴ + Dᴴ)⁻¹ * ((P' * B + Q' * D)ᴴ + Z * (P' * A + Q' * C)ᴴ) =
      Q'ᴴ + ((A * Z + B) * (C * Z + D)⁻¹) * P'ᴴ ∧
    ((P' * B + Q' * D) + (P' * A + Q' * C) * Z) * ((C * Z + D)⁻¹ * C) =
      (P' * A + Q' * C) - P' * (Z * Cᴴ + Dᴴ)⁻¹ ∧
    ((C * Z + D)⁻¹ * C) * ((P' * B + Q' * D)ᴴ + Z * (P' * A + Q' * C)ᴴ) =
      (P' * A + Q' * C)ᴴ - (C * Z + D)⁻¹ * P'ᴴ := by
  have hd := HAct.den'_act h1 h2 h3 h4 hQ
  have hJ : (C * Z + D) * (C * Z + D)⁻¹ = 1 := mul_nonsing_inv _ (Ne.isUnit hQ)
  have hJ' : (C * Z + D)⁻¹ * (C * Z + D) = 1 := nonsing_inv_mul _ (Ne.isUnit hQ)
  have r1 : ((P' * B + Q' * D) + (P' * A + Q' * C) * Z) * (C * Z + D)⁻¹ =
      Q' + P' * ((A * Z + B) * (C * Z + D)⁻¹) := by
    have : (P' * B + Q' * D) + (P' * A + Q' * C) * Z = Q' * (C * Z + D) + P' * (A * Z + B) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
    rw [this, Matrix.add_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, Matrix.mul_assoc]
  set W := (A * Z + B) * (C * Z + D)⁻¹ with hW
  have e1 : W * (C * Z + D) = A * Z + B := by
    rw [hW, Matrix.mul_assoc, hJ', Matrix.mul_one]
  have e2 : (Z * Cᴴ + Dᴴ) * (A - W * C) = 1 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hd]
    have e : (Z * Cᴴ + Dᴴ) * A - (Z * Aᴴ + Bᴴ) * C =
      Z * (Cᴴ * A) + Dᴴ * A - (Z * (Aᴴ * C) + Bᴴ * C) := by noncomm_ring
    rw [e, h1, h3]
    noncomm_ring
  have i2 : (Z * Cᴴ + Dᴴ)⁻¹ = A - W * C := inv_eq_right_inv e2
  have i2' : (Z * Cᴴ + Dᴴ)⁻¹ * (Z * Cᴴ + Dᴴ) = 1 := by rw [i2]; exact mul_eq_one_comm.1 e2
  have e3 : (Aᴴ - Cᴴ * W) * (C * Z + D) = 1 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, e1]
    have e : Aᴴ * (C * Z + D) - Cᴴ * (A * Z + B) =
      (Aᴴ * C) * Z + Aᴴ * D - ((Cᴴ * A) * Z + Cᴴ * B) := by noncomm_ring
    rw [e, h1, h2]
    noncomm_ring
  have i3 : (C * Z + D)⁻¹ = Aᴴ - Cᴴ * W := inv_eq_left_inv e3
  have s0 : (P' * B + Q' * D)ᴴ + Z * (P' * A + Q' * C)ᴴ = (Z * Cᴴ + Dᴴ) * (Q'ᴴ + W * P'ᴴ) := by
    rw [Matrix.mul_add (Z * Cᴴ + Dᴴ), ← Matrix.mul_assoc, hd]
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc]
    abel
  have k : (C * Z + D)⁻¹ * C * (Z * Cᴴ + Dᴴ) = Cᴴ := by
    have : C * (Z * Cᴴ + Dᴴ) = (C * Z + D) * Cᴴ := by
      rw [Matrix.mul_add, h5, Matrix.add_mul, Matrix.mul_assoc]
    rw [Matrix.mul_assoc, this, ← Matrix.mul_assoc, hJ', Matrix.one_mul]
  refine ⟨r1, ?_, ?_, ?_⟩
  · rw [s0, ← Matrix.mul_assoc, i2', Matrix.one_mul]
  · rw [← Matrix.mul_assoc, r1, i2]
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]; abel
  · rw [s0, ← Matrix.mul_assoc, k, i3]
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.mul_add, Matrix.sub_mul,
      Matrix.mul_assoc]
    abel
end GlobalTheory.SW.HeisH
