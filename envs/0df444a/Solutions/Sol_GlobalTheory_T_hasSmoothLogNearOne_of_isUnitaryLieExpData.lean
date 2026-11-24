-- Prove2me | solution 1 for GlobalTheory.T.hasSmoothLogNearOne_of_isUnitaryLieExpData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:21:18.120677+00:00
-- url     : https://prove2.me/submissions/4b146c62-ec2f-4f40-a792-deefbb95dce5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HasSmoothLogNearOneOfIsUnitaryLieExpData
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HasSmoothLogNearOneOfIsUnitaryLieExpDataStatement
import Theorems.Thm_GlobalTheory_SmoothForms_hasLog_of_isLieData


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j := by
  first | exact @GlobalTheory.SmoothForms.hasLog_of_isLieData | exact GlobalTheory.SmoothForms.hasLog_of_isLieData | (intros; apply GlobalTheory.SmoothForms.hasLog_of_isLieData <;> assumption)
end _root_.GlobalTheory.T
