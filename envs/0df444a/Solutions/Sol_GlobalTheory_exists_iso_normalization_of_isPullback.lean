-- Prove2me | solution 1 for GlobalTheory.exists_iso_normalization_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:37.880098+00:00
-- url     : https://prove2.me/submissions/c59a1697-ee99-4a89-8f70-46a683606293

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
theorem _root_.solution (h : IsPullback a f' f b) [PreservesNormalization b]
    {N' : Scheme.{u}} {c : N' ⟶ f.normalization} {d : N' ⟶ Y'}
    (h' : IsPullback c d f.fromNormalization b) {e : X' ⟶ N'}
    (hc : e ≫ c = a ≫ f.toNormalization) (hd : e ≫ d = f') :
    ∃ i : f'.normalization ≅ N', f'.toNormalization ≫ i.hom = e ∧
      i.hom ≫ d = f'.fromNormalization ∧ i.hom ≫ c = normalizationMap f' f a b h.w := by
  refine ⟨(isPullback_normalizationMap h).isoIsPullback _ _ h', ?_, by simp, by simp⟩
  apply h'.hom_ext <;> simp [hc, hd]
end GlobalTheory
