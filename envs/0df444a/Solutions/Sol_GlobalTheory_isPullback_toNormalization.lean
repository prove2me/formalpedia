-- Prove2me | solution 1 for GlobalTheory.isPullback_toNormalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:39:47.461701+00:00
-- url     : https://prove2.me/submissions/04489372-5a3c-4781-ae36-5eef9af239ae

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
variable {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {a : X' ⟶ X} {b : Y' ⟶ Y}
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
namespace GlobalTheory
theorem _root_.solution (h : IsPullback a f' f b) [PreservesNormalization b] :
    IsPullback a f'.toNormalization f.toNormalization (normalizationMap f' f a b h.w) :=
  IsPullback.of_bot (by simpa using h) (by simp) (isPullback_normalizationMap h)
end GlobalTheory
