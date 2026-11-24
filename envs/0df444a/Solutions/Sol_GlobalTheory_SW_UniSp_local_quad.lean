-- Prove2me | solution 1 for GlobalTheory.SW.UniSp.local_quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:29:38.824853+00:00
-- url     : https://prove2.me/submissions/29bb10f4-445e-4c2d-afbd-a6453cafe2cf

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
variable {m o : Type} [Fintype m] [Fintype o] [DecidableEq o]
variable [DecidableEq m]
namespace GlobalTheory.SW.UniSp
theorem _root_.solution {C D Z : Matrix m m ℂ} (h4 : C * Dᴴ = D * Cᴴ) (hP : (Z * Cᴴ + Dᴴ).det ≠ 0)
    (hQ : (C * Z + D).det ≠ 0) (z z' : m → ℂ) :
    Sum.elim z z' ⬝ᵥ (fromBlocks ((Z * Cᴴ + Dᴴ)⁻¹)ᵀ 0 0 (C * Z + D)⁻¹ * (sw m * dl C)) *ᵥ
      Sum.elim z z' = 2 * (z' ⬝ᵥ ((C * Z + D)⁻¹ * C) *ᵥ z) := by
  have e : Cᴴ * (Z * Cᴴ + Dᴴ)⁻¹ = (C * Z + D)⁻¹ * C := by
    have e0 : (C * Z + D) * Cᴴ = C * (Z * Cᴴ + Dᴴ) := by
      rw [Matrix.add_mul, Matrix.mul_add, h4, Matrix.mul_assoc]
    calc _ = (C * Z + D)⁻¹ * ((C * Z + D) * Cᴴ) * (Z * Cᴴ + Dᴴ)⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit hQ), Matrix.one_mul]
      _ = _ := by
          rw [e0, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hP),
            Matrix.mul_one]
  simp only [dl, sw, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.one_mul, add_zero, zero_add, ← transpose_mul, e, fromBlocks_mulVec, zero_mulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
  rw [mulVec_transpose, dotProduct_comm z, ← dotProduct_mulVec, two_mul]
end GlobalTheory.SW.UniSp
