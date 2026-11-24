-- Prove2me | solution 1 for GlobalTheory.isOpenImmersion_lift_toNormalization_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:06.328081+00:00
-- url     : https://prove2.me/submissions/357ba4fb-3a60-4314-aecb-e4dd11452d99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Theorems.Thm_GlobalTheory_isOpenImmersion_of_isPullback_normalization
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
theorem _root_.solution [QuasiCompact f'] [LocallyQuasiFinite f']
    [LocallyOfFiniteType f'] [IsSeparated f'] :
    IsOpenImmersion (pullback.lift f.toNormalization f' (by simp [H]) :
        X ⟶ pullback f.fromNormalization b) ∧
      IsSchemeTheoreticallyDominant (pullback.lift f.toNormalization f' (by simp [H]) :
        X ⟶ pullback f.fromNormalization b) ∧
      IsDominant (pullback.lift f.toNormalization f' (by simp [H]) :
        X ⟶ pullback f.fromNormalization b) :=
  isOpenImmersion_of_isPullback_normalization (isPullback_id_of_mono f' b f H)
    (.of_hasPullback _ _) (by simp [pullback.lift_fst]) (pullback.lift_snd ..)
end GlobalTheory
