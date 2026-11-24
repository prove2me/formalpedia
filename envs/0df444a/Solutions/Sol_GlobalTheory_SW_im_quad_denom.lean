-- Prove2me | solution 1 for GlobalTheory.SW.im_quad_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:47:08.373706+00:00
-- url     : https://prove2.me/submissions/7192884d-44ff-4c13-9db7-d2d41cb9ef07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Theorems.Thm_GlobalTheory_SW_im_quad_eq_re_imH
import Theorems.Thm_GlobalTheory_SW_imH_mul_denom

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
    (x : Fin N → ℂ) :
    (star x ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ x)).im =
      -(star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re := by
  have e : star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x) = star x ⬝ᵥ (C * imH Z * Cᴴ) *ᵥ x := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  rw [e, mulVec_mulVec, im_quad_eq_re_imH, imH_mul_denom C D Z h, neg_mulVec, dotProduct_neg,
    Complex.neg_re]
end GlobalTheory.SW
