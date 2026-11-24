-- Prove2me | solution 1 for GlobalTheory.existsUnique_linear_lift_of_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:06:05.176797+00:00
-- url     : https://prove2.me/submissions/d5a548f2-de62-4cba-920d-584114d26f2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Theorems.Thm_GlobalTheory_realLinear_lift_eq_fderiv
import Theorems.Thm_GlobalTheory_apply_fderiv_eq_of_germ

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
    (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) :
    ∃! L : V →L[𝕜] W, ∀ z, ex' (L z) = ex z := by
  refine ⟨fderiv 𝕜 g 0, apply_fderiv_eq_of_germ hker hd hg, fun L hL ↦ ?_⟩
  have := realLinear_lift_eq_fderiv hker hd hg (L := L.restrictScalars ℝ) hL
  ext z
  exact DFunLike.congr_fun this z
end GlobalTheory
