-- Prove2me | solution 1 for GlobalTheory.AnisoSize.house_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:04.243407+00:00
-- url     : https://prove2.me/submissions/c71f20b6-d2ad-4691-a52b-2b59da5cd76a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector

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
theorem _root_.solution {a : E} {T : ℝ} (hT : 0 ≤ T) (h : ∀ φ : E →+* ℂ, ‖φ a‖ ≤ T) : house a ≤ T :=
  (pi_norm_le_iff_of_nonneg hT).2 h
end GlobalTheory.AnisoSize
