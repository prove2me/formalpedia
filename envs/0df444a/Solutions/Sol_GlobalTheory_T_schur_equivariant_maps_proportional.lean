-- Prove2me | solution 1 for GlobalTheory.T.schur_equivariant_maps_proportional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:55.027042+00:00
-- url     : https://prove2.me/submissions/851f8ca6-8442-47ca-929f-71e480b23ea2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SchurEquivariantMapsProportional
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SchurEquivariantMapsProportionalStatement
import Theorems.Thm_GlobalTheory_schur_proportional


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (H W X : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] [AddCommGroup X] [Module ℂ X] (ρ : H → Module.End ℂ W) (a : H → Module.End ℂ X) (φ ξ : W →ₗ[ℂ] X), (∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤) → Function.Injective ξ → LinearMap.range φ ≤ LinearMap.range ξ → (∀ h w, φ (ρ h w) = a h (φ w)) → (∀ h w, ξ (ρ h w) = a h (ξ w)) → ∃ c : ℂ, φ = c • ξ := by
  first | exact @GlobalTheory.schur_proportional | exact GlobalTheory.schur_proportional | (intros; apply GlobalTheory.schur_proportional <;> assumption)
end _root_.GlobalTheory.T
