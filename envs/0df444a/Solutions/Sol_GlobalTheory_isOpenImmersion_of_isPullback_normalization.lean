-- Prove2me | solution 1 for GlobalTheory.isOpenImmersion_of_isPullback_normalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:04:58.90704+00:00
-- url     : https://prove2.me/submissions/20de9fd0-d7dc-492b-86fe-d993e72b7601

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Theorems.Thm_GlobalTheory_exists_iso_normalization_of_isPullback

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
    [PreservesNormalization b] [LocallyQuasiFinite f'] [LocallyOfFiniteType f'] [IsSeparated f']
    {N' : Scheme.{u}} {c : N' ⟶ f.normalization} {d : N' ⟶ Y'}
    (h' : IsPullback c d f.fromNormalization b) {e : X' ⟶ N'}
    (hc : e ≫ c = a ≫ f.toNormalization) (hd : e ≫ d = f') :
    IsOpenImmersion e ∧ IsSchemeTheoreticallyDominant e ∧ IsDominant e := by
  obtain ⟨i, rfl, -⟩ := exists_iso_normalization_of_isPullback h h' hc hd
  exact ⟨inferInstance, inferInstance, inferInstance⟩
end GlobalTheory
