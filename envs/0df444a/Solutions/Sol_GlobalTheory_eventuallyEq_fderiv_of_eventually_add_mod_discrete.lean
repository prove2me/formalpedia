-- Prove2me | solution 1 for GlobalTheory.eventuallyEq_fderiv_of_eventually_add_mod_discrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:37:58.154077+00:00
-- url     : https://prove2.me/submissions/9036a80d-b6ae-4449-b409-e3a436d462b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Theorems.Thm_GlobalTheory_existsUnique_realLinear_of_eventually_add_mod_discrete
import Theorems.Thm_GlobalTheory_realLinear_eq_fderiv_of_eventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [IsScalarTower ℝ 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W]
namespace GlobalTheory
theorem _root_.solution {Γ : AddSubgroup W}
    (hΓ : IsDiscrete (Γ : Set W)) {g : V → W} (hd : DifferentiableAt 𝕜 g 0) (h0 : g 0 = 0)
    (hg : ∀ᶠ p : V × V in 𝓝 0, g (p.1 + p.2) - g p.1 - g p.2 ∈ Γ) :
    g =ᶠ[𝓝 0] fderiv 𝕜 g 0 := by
  obtain ⟨L, hL, -⟩ :=
    existsUnique_realLinear_of_eventually_add_mod_discrete hΓ hd.continuousAt h0 hg
  have := realLinear_eq_fderiv_of_eventuallyEq hd (L := L) (c := 0)
    (hL.mono fun z hz ↦ by rw [hz, add_zero])
  rw [this] at hL
  exact hL
end GlobalTheory
