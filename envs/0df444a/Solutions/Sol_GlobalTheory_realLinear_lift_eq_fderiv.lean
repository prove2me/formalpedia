-- Prove2me | solution 1 for GlobalTheory.realLinear_lift_eq_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:46:53.11669+00:00
-- url     : https://prove2.me/submissions/974794b1-1f22-480d-a629-cce8ceec9ef5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Theorems.Thm_GlobalTheory_realLinear_eq_fderiv_of_eventuallyEq
import Theorems.Thm_GlobalTheory_eventually_eq_lift_add

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
  {A : Type*} [AddCommGroup A]
namespace GlobalTheory
theorem _root_.solution {ex : V →+ A} {ex' : W →+ A}
    (hker : IsDiscrete (ex'.ker : Set W)) {g : V → W} (hd : DifferentiableAt 𝕜 g 0)
    (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) {L : V →L[ℝ] W} (hL : ∀ z, ex' (L z) = ex z) :
    L = (fderiv 𝕜 g 0).restrictScalars ℝ :=
  realLinear_eq_fderiv_of_eventuallyEq hd (eventually_eq_lift_add hker hd.continuousAt hg hL)
end GlobalTheory
