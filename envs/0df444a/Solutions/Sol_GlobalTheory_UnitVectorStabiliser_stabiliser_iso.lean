-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabiliser.stabiliser_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:52.543524+00:00
-- url     : https://prove2.me/submissions/80fc312b-1d3e-4ca4-9817-421f74a327d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Theorems.Thm_GlobalTheory_UnitVectorStabiliser_restrHom_injective
import Theorems.Thm_GlobalTheory_UnitVectorStabiliser_restrHom_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.UnitVectorStabiliser
namespace GlobalTheory.UnitVectorStabiliser
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (OEv F E v) (Fin M → Ev F E v)), ∀ x : Fin M → Ev F E v, IsUnit (hR (Fv F v) σ J x x) → ∃ φ : (stabLat σ J v (perpLat σ J v L x) ⊓ stabVec σ J v x : Subgroup (HA (Fv F v) σ J)) ≃* unitaryLatIn σ J v (perp σ J v x) (perpLat σ J v L x), ∀ g (y : perp σ J v x), (((φ g : perp σ J v x ≃ₗ[Ev F E v] perp σ J v x) y : perp σ J v x) : Fin M → Ev F E v) = act σ J v (g : HA (Fv F v) σ J) y := by
  intro F E _ _ _ _ _ σ h M J hJ v L x hx
  exact ⟨MulEquiv.ofBijective (restrHom σ J v (perpLat σ J v L x) x)
    ⟨restrHom_injective σ J v _ x hx, restrHom_surjective σ J v h hJ L x hx⟩, fun _ _ => rfl⟩
end GlobalTheory.UnitVectorStabiliser
