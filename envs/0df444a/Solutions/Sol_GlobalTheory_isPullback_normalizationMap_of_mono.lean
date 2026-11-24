-- Prove2me | solution 1 for GlobalTheory.isPullback_normalizationMap_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:04.935722+00:00
-- url     : https://prove2.me/submissions/a70a68f5-cb2d-42e1-8c9a-1c418fd34380

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Theorems.Thm_GlobalTheory_isPullback_id_of_mono

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
variable [QuasiCompact f] [QuasiSeparated f] [PreservesNormalization b]
include H
namespace GlobalTheory
theorem _root_.solution [QuasiCompact f'] [QuasiSeparated f'] :
    IsPullback (normalizationMap f' f (𝟙 X) b (by simp [H])) f'.fromNormalization
      f.fromNormalization b :=
  isPullback_normalizationMap (isPullback_id_of_mono f' b f H)
end GlobalTheory
