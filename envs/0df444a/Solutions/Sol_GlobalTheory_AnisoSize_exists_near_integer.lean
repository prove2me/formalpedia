-- Prove2me | solution 1 for GlobalTheory.AnisoSize.exists_near_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:04.951635+00:00
-- url     : https://prove2.me/submissions/bcc0aa5b-0ff7-4227-8282-a822d50ed089

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
import Theorems.Thm_GlobalTheory_AnisoSize_norm_le_house
import Theorems.Thm_GlobalTheory_AnisoSize_house_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix Module Submodule
open scoped ContDiff Topology nonZeroDivisors
open GlobalTheory GlobalTheory.AnisoSize
variable {E : Type} [Field E] [NumberField E]
variable (E)
namespace GlobalTheory.AnisoSize
theorem _root_.solution : ∃ C : ℝ, ∀ c : E, ∃ t : E, IsIntegral ℤ t ∧ house (c - t) ≤ C := by
  classical
  let b := integralBasis E
  refine ⟨∑ i, house (b i), fun c => ⟨∑ i, (⌊b.repr c i⌋ : E) * b i, ?_, ?_⟩⟩
  · refine IsIntegral.sum _ fun i _ => (isIntegral_intCast _).mul ?_
    rw [integralBasis_apply]; exact (RingOfIntegers.basis E i).isIntegral_coe
  · have h1 : c - ∑ i, (⌊b.repr c i⌋ : E) * b i = ∑ i, (Int.fract (b.repr c i) : ℚ) • b i := by
      conv_lhs => rw [← b.sum_repr c]
      simp only [b.repr_sum_self, Int.fract, sub_smul, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul,
        zsmul_eq_mul, b.sum_repr]
    rw [h1]
    refine (house_sum_le_sum_house _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine house_le (house_nonneg _) fun φ => ?_
    rw [map_rat_smul, ← Rat.cast_smul_eq_qsmul ℝ, norm_smul]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (norm_le_house φ _)
    rw [Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast Int.fract_nonneg _)]
    exact_mod_cast (Int.fract_lt_one _).le
end GlobalTheory.AnisoSize
