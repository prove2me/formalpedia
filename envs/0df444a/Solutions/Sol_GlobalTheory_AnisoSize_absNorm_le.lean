-- Prove2me | solution 1 for GlobalTheory.AnisoSize.absNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:31:33.532809+00:00
-- url     : https://prove2.me/submissions/465f1340-fe27-49aa-9781-d7b1f27c8fb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
import Theorems.Thm_GlobalTheory_AnisoSize_norm_le_house
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
theorem _root_.solution (a : 𝓞 E) :
    (Ideal.absNorm (Ideal.span {a}) : ℝ) ≤ house (algebraMap (𝓞 E) E a) ^ finrank ℚ E := by
  rw [absNorm_eq, ← Embeddings.card E ℂ, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun φ _ => norm_le_house φ _
end GlobalTheory.AnisoSize
