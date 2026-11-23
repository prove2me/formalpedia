-- Prove2me | solution 1 for GlobalTheory.isPullback_id_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:10.386825+00:00
-- url     : https://prove2.me/submissions/30bb1f98-6b6f-4ca6-b6de-4ab51a0f31b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
attribute [instance] PreservesNormalization.isIso_normalizationPullback
variable {X Y V : Scheme.{u}} (f' : X ⟶ V) (b : V ⟶ Y) [Mono b] (f : X ⟶ Y) (H : f = f' ≫ b)
include H
namespace GlobalTheory
theorem _root_.solution : IsPullback (𝟙 X) f' f b :=
  IsPullback.of_horiz_isIso_mono ⟨by simp [H]⟩
end GlobalTheory
