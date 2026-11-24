-- Prove2me | solution 1 for GlobalTheory.isPullback_toNormalization_of_isIntegralHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:07.19009+00:00
-- url     : https://prove2.me/submissions/e9aa0176-eceb-4f8e-ae17-8dd2ff690033

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
theorem _root_.solution (h : IsPullback a f' f b)
    [PreservesNormalization b] [IsIntegralHom f'] :
    IsPullback (a ≫ f.toNormalization) f' f.fromNormalization b :=
  (isPullback_normalizationMap h).of_iso (asIso f'.toNormalization).symm (.refl _) (.refl _)
    (.refl _) (by simp) (by simp) (by simp) (by simp)
end GlobalTheory
