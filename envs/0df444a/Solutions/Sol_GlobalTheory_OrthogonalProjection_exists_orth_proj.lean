-- Prove2me | solution 1 for GlobalTheory.OrthogonalProjection.exists_orth_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:34:06.809774+00:00
-- url     : https://prove2.me/submissions/8d8c8834-386d-4a34-a581-247be0a3e7e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOrthogonalProjectionFinite
import Theorems.Thm_GlobalTheory_OrthogonalProjection_exists_orthogonal_projection_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrthogonalProjection
open Module
namespace GlobalTheory.OrthogonalProjection
theorem _root_.solution : ∀ {W : Type} [inst : AddCommGroup W] [inst_1 : Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ (v : W), ((B : W → W →ₗ[ℂ] ℂ) v : W → ℂ) v = (0 : ℂ) → v = (0 : W)) → ∀ (M : Submodule ℂ W) [FiniteDimensional ℂ ↥M] (v : W), ∃ m ∈ M, ∀ z ∈ M, ((B : W → W →ₗ[ℂ] ℂ) z : W → ℂ) (v - m) = (0 : ℂ) := by
  intro W _ _ B hB M _ v
  exact exists_orthogonal_projection_finite B hB M v
end GlobalTheory.OrthogonalProjection
