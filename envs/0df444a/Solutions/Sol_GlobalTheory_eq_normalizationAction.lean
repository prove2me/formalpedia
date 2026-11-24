-- Prove2me | solution 1 for GlobalTheory.eq_normalizationAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:37:04.06197+00:00
-- url     : https://prove2.me/submissions/c4d519e6-b7b9-4510-8954-39f4cbbb6f7a

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
variable {G : Type v} [Group G] {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
variable (ρ : G →* Aut X) (σ : G →* Aut Y) (H : ∀ g, (ρ g).hom ≫ f = f ≫ (σ g).hom)
namespace GlobalTheory
theorem _root_.solution (τ : G →* Aut f.normalization)
    (h₁ : ∀ g, f.toNormalization ≫ (τ g).hom = (ρ g).hom ≫ f.toNormalization)
    (h₂ : ∀ g, (τ g).hom ≫ f.fromNormalization = f.fromNormalization ≫ (σ g).hom) :
    τ = normalizationAction f ρ σ H :=
  MonoidHom.ext fun g ↦ Iso.ext (eq_normalizationMap f f _ _ (H g) (h₁ g) (h₂ g))
end GlobalTheory
