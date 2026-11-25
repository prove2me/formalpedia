-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.lintegral_conv_sq_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:33:35.916126+00:00
-- url     : https://prove2.me/submissions/aad4c0fd-5e3a-48c2-8913-276174cad83c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_lintegral_conv_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {K G : E → ℝ≥0∞} (hK : Measurable K) (hG : Measurable G) :
    ∫⁻ ξ, (∫⁻ η, K (ξ - η) * G η) ^ 2 ≤ (∫⁻ ζ, K ζ) ^ 2 * ∫⁻ η, G η ^ 2 := by
  have hm : Measurable (Function.uncurry fun ξ η : E ↦ K (ξ - η) * G η ^ 2) :=
    (hK.comp (measurable_fst.sub measurable_snd)).mul ((hG.pow_const 2).comp measurable_snd)
  calc ∫⁻ ξ, (∫⁻ η, K (ξ - η) * G η) ^ 2
      ≤ ∫⁻ ξ, (∫⁻ ζ, K ζ) * ∫⁻ η, K (ξ - η) * G η ^ 2 :=
        lintegral_mono fun ξ ↦ lintegral_conv_sq_le hK hG ξ
    _ = (∫⁻ ζ, K ζ) * ∫⁻ ξ, ∫⁻ η, K (ξ - η) * G η ^ 2 :=
        lintegral_const_mul _ hm.lintegral_prod_right'
    _ = (∫⁻ ζ, K ζ) * ∫⁻ η, ∫⁻ ξ, K (ξ - η) * G η ^ 2 := by
        rw [lintegral_lintegral_swap hm.aemeasurable]
    _ = (∫⁻ ζ, K ζ) * ∫⁻ η, (∫⁻ ζ, K ζ) * G η ^ 2 := by
        congr 1; apply lintegral_congr; intro η
        rw [lintegral_mul_const _ (show Measurable fun ξ : E ↦ K (ξ - η) from
          hK.comp (measurable_id.sub measurable_const)), lintegral_sub_right_eq_self K η]
    _ = _ := by rw [lintegral_const_mul _ (hG.pow_const 2)]; ring
end GroundTheory.Automorphic.Sobolev
