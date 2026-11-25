-- Prove2me | solution 1 for GlobalTheory.SW.EisSiegel.det_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:56:04.746267+00:00
-- url     : https://prove2.me/submissions/27831638-6e1f-4516-9413-e8e8d3bcb053

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelOperatorHermitianEisensteinSeries
import Theorems.Thm_GlobalTheory_SW_im_quad_denom
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisSiegel
variable {N : ℕ}
namespace GlobalTheory.SW.EisSiegel
theorem _root_.solution (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : D * Cᴴ = C * Dᴴ)
    (hQ : (C * Z + D).det ≠ 0) (hZ : (imH Z).PosDef) (v : Fin N → ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ (C *ᵥ v ≠ 0 → 0 < c) ∧ ∀ t : ℝ, ‖(C * Z + D).det‖ * (1 + t * c) ≤
      ‖(C * (Z + (I * t) • vecMulVec v (star v)) + D).det‖ := by
  have hH : (C * Dᴴ).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, h]
  set Q := C * Z + D with hQdef
  have hU : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ
  set x : Fin N → ℂ := (Q⁻¹)ᴴ *ᵥ v with hx
  have hxv : Qᴴ *ᵥ x = v := by
    rw [hx, mulVec_mulVec, ← conjTranspose_mul, nonsing_inv_mul _ hU, conjTranspose_one, one_mulVec]
  have hsx : star x = star v ᵥ* Q⁻¹ := by
    rw [hx, star_mulVec, conjTranspose_conjTranspose]
  have hs := im_quad_denom C D Z hH x
  rw [← hQdef, hxv] at hs
  refine ⟨(star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re,
    (Complex.nonneg_iff.1 (hZ.posSemidef.dotProduct_mulVec_nonneg (Cᴴ *ᵥ x))).1,
    fun hv => (Complex.pos_iff.1 (hZ.dotProduct_mulVec_pos fun h0 => hv ?_)).1, fun t => ?_⟩
  · rw [← hxv, hQdef, conjTranspose_add, conjTranspose_mul, add_mulVec, ← mulVec_mulVec x Zᴴ, h0,
      mulVec_zero, zero_add, mulVec_mulVec, ← h, ← mulVec_mulVec, h0, mulVec_zero]
  · have e : C * (Z + (I * t) • vecMulVec v (star v)) + D =
        Q * (1 + vecMulVec ((I * t) • (Q⁻¹ *ᵥ (C *ᵥ v))) (star v)) := by
      rw [Matrix.mul_add Q, Matrix.mul_one, mul_vecMulVec, mulVec_smul, mulVec_mulVec,
        mul_nonsing_inv _ hU, one_mulVec, Matrix.mul_add, ← smul_vecMulVec, mul_vecMulVec,
        mulVec_smul, hQdef]
      abel
    rw [e, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, norm_mul,
      dotProduct_smul, dotProduct_mulVec (star v), ← hsx]
    generalize (star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re = c at hs
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) (Complex.re_le_norm _)) (norm_nonneg _)
    simp only [smul_eq_mul, add_re, one_re, mul_re, mul_im, I_re, I_im, zero_mul, one_mul,
      ofReal_re, ofReal_im, hs]
    ring
end GlobalTheory.SW.EisSiegel
