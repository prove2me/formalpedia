-- Prove2me | solution 1 for GlobalTheory.SW.posSemidef_sub_mul_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:45:34.767795+00:00
-- url     : https://prove2.me/submissions/d756438b-d25b-4ee3-a1aa-3c428f70df0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Theorems.Thm_GlobalTheory_SW_star_dotProduct_self_eq_sum

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
theorem _root_.solution (X : Matrix (Fin N) (Fin N) ℂ) (B : ℝ)
    (hX : ∀ a b, ‖X a b‖ ≤ B) :
    ((((N : ℝ) ^ 2 * B ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine IsHermitian.sub ?_ (isHermitian_mul_conjTranspose_self X)
    simp [IsHermitian]
  · have h1 : star x ⬝ᵥ (X * Xᴴ) *ᵥ x = star (Xᴴ *ᵥ x) ⬝ᵥ (Xᴴ *ᵥ x) := by
      rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec, mulVec_mulVec]
    rw [sub_mulVec, dotProduct_sub, h1, smul_mulVec, one_mulVec, dotProduct_smul,
      star_dotProduct_self_eq_sum, star_dotProduct_self_eq_sum, smul_eq_mul, ← ofReal_mul,
      ← ofReal_sub, Complex.zero_le_real, sub_nonneg]
    have h2 : ∀ a, ‖(Xᴴ *ᵥ x) a‖ ^ 2 ≤ B ^ 2 * (N * ∑ b, ‖x b‖ ^ 2) := by
      intro a
      have h3 : ‖(Xᴴ *ᵥ x) a‖ ≤ B * ∑ b, ‖x b‖ := by
        rw [Finset.mul_sum]
        refine (norm_sum_le Finset.univ fun b => Xᴴ a b * x b).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul, conjTranspose_apply, norm_star]
        exact mul_le_mul_of_nonneg_right (hX b a) (norm_nonneg _)
      have h4 : (∑ b, ‖x b‖) ^ 2 ≤ N * ∑ b, ‖x b‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun b => ‖x b‖)
      calc ‖(Xᴴ *ᵥ x) a‖ ^ 2 ≤ (B * ∑ b, ‖x b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
        _ = B ^ 2 * (∑ b, ‖x b‖) ^ 2 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 (sq_nonneg B)
    refine (Finset.sum_le_sum fun a _ => h2 a).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
end GlobalTheory.SW
