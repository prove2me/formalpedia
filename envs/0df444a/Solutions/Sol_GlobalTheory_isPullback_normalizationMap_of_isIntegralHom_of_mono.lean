-- Prove2me | solution 1 for GlobalTheory.isPullback_normalizationMap_of_isIntegralHom_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:39:45.007123+00:00
-- url     : https://prove2.me/submissions/c85f015c-14dc-4b8d-bd89-9238b52c93c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Theorems.Thm_GlobalTheory_isPullback_normalizationMap_of_mono

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
namespace GlobalTheory
theorem _root_.solution {X T V Y : Scheme.{u}} (f₁ : X ⟶ T)
    (c : T ⟶ V) [IsIntegralHom c] (b : V ⟶ Y) [Mono b] [PreservesNormalization b] (f : X ⟶ Y)
    (H : f = f₁ ≫ c ≫ b) [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f₁]
    [QuasiSeparated f₁] :
    IsPullback (normalizationMap f₁ f (𝟙 X) (c ≫ b) (by simp [H])) (f₁.fromNormalization ≫ c)
      f.fromNormalization b :=
  (isPullback_normalizationMap_of_mono (f₁ ≫ c) b f (by simp [H])).of_iso
    (normalizationTransIso f₁ c (f₁ ≫ c) rfl).symm (.refl _) (.refl _) (.refl _)
    (by simp [Iso.eq_inv_comp, normalizationTransIso, normalizationMap_comp])
    (by simp [Iso.eq_inv_comp]) (by simp) (by simp)
end GlobalTheory
