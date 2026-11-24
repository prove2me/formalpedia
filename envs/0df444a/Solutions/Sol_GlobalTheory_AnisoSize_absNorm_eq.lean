-- Prove2me | solution 1 for GlobalTheory.AnisoSize.absNorm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:15:57.859089+00:00
-- url     : https://prove2.me/submissions/96cc9331-09c2-4074-ab3b-52d8f75bf677

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
import Theorems.Thm_GlobalTheory_AnisoSize_abs_norm_eq

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
    (Ideal.absNorm (Ideal.span {a}) : ℝ) = ∏ φ : E →+* ℂ, ‖φ (algebraMap (𝓞 E) E a)‖ := by
  rw [← abs_norm_eq, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp
end GlobalTheory.AnisoSize
