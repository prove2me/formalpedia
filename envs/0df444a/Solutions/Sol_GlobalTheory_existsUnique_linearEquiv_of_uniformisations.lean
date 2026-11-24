-- Prove2me | solution 1 for GlobalTheory.existsUnique_linearEquiv_of_uniformisations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:50.349317+00:00
-- url     : https://prove2.me/submissions/f5074b92-6f83-4096-8f90-4e4cc56d5a68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Theorems.Thm_GlobalTheory_countable_of_isDiscrete_finiteDimensional
import Theorems.Thm_GlobalTheory_existsUnique_linearEquiv_lift_of_countable_ker

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
theorem _root_.solution [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ W] {ex : V →+ A} {ex' : W →+ A} (hk : IsDiscrete (ex.ker : Set V))
    (hk' : IsDiscrete (ex'.ker : Set W)) (hr : ex'.range ≤ ex.range) {g : V → W}
    (hd : DifferentiableAt 𝕜 g 0) (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) :
    ∃! L : V ≃L[𝕜] W, (∀ z, ex' (L z) = ex z) ∧ ex.ker.map (L : V →+ W) = ex'.ker :=
  existsUnique_linearEquiv_lift_of_countable_ker (countable_of_isDiscrete_finiteDimensional hk)
    hk' hr hd hg
end GlobalTheory
