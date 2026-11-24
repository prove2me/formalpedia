-- Prove2me | solution 1 for GlobalTheory.AnisoSize.house_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:31:37.27991+00:00
-- url     : https://prove2.me/submissions/4c195501-94ca-4ef3-8179-acd8318e5010

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
import Theorems.Thm_GlobalTheory_AnisoSize_norm_le_house
import Theorems.Thm_GlobalTheory_AnisoSize_house_le
import Theorems.Thm_GlobalTheory_AnisoSize_absNorm_eq

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
namespace GlobalTheory.AnisoSize
theorem _root_.solution {a : E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0) {T : ℝ} (hT : 1 ≤ T)
    (h : house a ≤ T) : house a⁻¹ ≤ T ^ finrank ℚ E := by
  classical
  refine house_le (by positivity) fun φ => ?_
  let a' : 𝓞 E := ⟨a, ha⟩
  have h1 : (1 : ℝ) ≤ Ideal.absNorm (Ideal.span {a'}) := by
    have : Ideal.absNorm (Ideal.span {a'}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact fun h => h0 (congrArg Subtype.val h)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  rw [absNorm_eq, ← Finset.mul_prod_erase _ _ (Finset.mem_univ φ)] at h1
  have h2 : ∏ ψ ∈ Finset.univ.erase φ, ‖ψ (algebraMap (𝓞 E) E a')‖ ≤ T ^ finrank ℚ E := by
    calc _ ≤ ∏ _ψ ∈ Finset.univ.erase φ, T :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun ψ _ => (norm_le_house ψ _).trans h
      _ ≤ _ := by
          rw [Finset.prod_const, ← Embeddings.card E ℂ]
          exact pow_le_pow_right₀ hT (Finset.card_le_univ _)
  have h3 : 0 < ‖φ a‖ := norm_pos_iff.2 ((map_ne_zero φ).2 h0)
  rw [map_inv₀, norm_inv, inv_le_iff_one_le_mul₀' h3]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 h3.le)
end GlobalTheory.AnisoSize
