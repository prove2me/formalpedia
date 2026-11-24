-- Prove2me | solution 1 for GlobalTheory.SW.norm_det_denom_le_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:14:58.83438+00:00
-- url     : https://prove2.me/submissions/7f792b49-224c-4046-a7ca-968c2a7a5708

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Theorems.Thm_GlobalTheory_SW_im_quad_denom
import Theorems.Thm_GlobalTheory_SW_det_denom_ne_zero

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
open GlobalTheory GlobalTheory.SW
variable {N : ℕ}
namespace GlobalTheory.SW
theorem _root_.solution (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hp : (C * Cᴴ + D * Dᴴ).PosDef) (hZ : (imH Z).PosDef) (v : Fin N → ℂ) :
    ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • vecMulVec v (star v)) + D).det‖ := by
  have hW := det_denom_ne_zero C D Z h hp hZ
  have hWh : IsUnit ((C * Z + D)ᴴ).det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hW)
  obtain ⟨y, rfl⟩ : ∃ y, (C * Z + D)ᴴ *ᵥ y = v :=
    ⟨((C * Z + D)ᴴ)⁻¹ *ᵥ v, by rw [mulVec_mulVec, mul_nonsing_inv (A := (C * Z + D)ᴴ) hWh, one_mulVec]⟩
  have hstar : star ((C * Z + D)ᴴ *ᵥ y) = star y ᵥ* (C * Z + D) := by
    rw [star_mulVec, conjTranspose_conjTranspose]
  have e1 : I • vecMulVec (C *ᵥ ((C * Z + D)ᴴ *ᵥ y)) (star y ᵥ* (C * Z + D)) =
      vecMulVec (I • (C *ᵥ ((C * Z + D)ᴴ *ᵥ y))) (star y) * (C * Z + D) := by
    rw [vecMulVec_mul]
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have key : C * (Z + I • vecMulVec ((C * Z + D)ᴴ *ᵥ y) (star ((C * Z + D)ᴴ *ᵥ y))) + D =
      (1 + vecMulVec (I • (C *ᵥ ((C * Z + D)ᴴ *ᵥ y))) (star y)) * (C * Z + D) := by
    rw [hstar, Matrix.mul_add C, Matrix.mul_smul C, mul_vecMulVec C, e1,
      Matrix.add_mul (1 : Matrix (Fin N) (Fin N) ℂ), Matrix.one_mul]
    abel
  have hs : (star y ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ y)).im ≤ 0 := by
    rw [im_quad_denom C D Z h y]
    have h0 := (Complex.nonneg_iff.mp (hZ.posSemidef.dotProduct_mulVec_nonneg (Cᴴ *ᵥ y))).1
    linarith
  have hone : 1 ≤ ‖1 + I * (star y ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ y))‖ := by
    refine le_trans ?_ ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub]
    linarith
  rw [key, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul, norm_mul]
  exact le_mul_of_one_le_left (norm_nonneg _) hone
end GlobalTheory.SW
