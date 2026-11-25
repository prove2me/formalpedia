-- Prove2me | solution 1 for GroundTheory.Automorphic.shortBasisBound_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:18.018005+00:00
-- url     : https://prove2.me/submissions/da15dd71-ad8d-49eb-a34f-ae259556ff2c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Submodule
open scoped RealInnerProductSpace
universe u
namespace GroundTheory.Automorphic
theorem _root_.solution : ∀ (N : ℕ) {μ : ℝ}, 0 < μ → 0 ≤ shortBasisBound N μ
  | 0, _, _ => le_rfl
  | N + 1, μ, hμ => by
    have h3 : 0 < Real.sqrt 3 / 2 * μ := by positivity
    have := solution N h3
    simp only [shortBasisBound]
    positivity
end GroundTheory.Automorphic
