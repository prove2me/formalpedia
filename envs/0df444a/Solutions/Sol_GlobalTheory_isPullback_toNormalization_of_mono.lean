-- Prove2me | solution 1 for GlobalTheory.isPullback_toNormalization_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:08.064285+00:00
-- url     : https://prove2.me/submissions/de5dfea5-ffca-4c6b-ba27-6bc626b554e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Theorems.Thm_GlobalTheory_isPullback_toNormalization_of_isIntegralHom
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
theorem _root_.solution [IsIntegralHom f'] :
    IsPullback f.toNormalization f' f.fromNormalization b := by
  simpa using isPullback_toNormalization_of_isIntegralHom (isPullback_id_of_mono f' b f H)
end GlobalTheory
