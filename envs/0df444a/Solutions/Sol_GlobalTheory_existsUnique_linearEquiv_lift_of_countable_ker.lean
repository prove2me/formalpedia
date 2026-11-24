-- Prove2me | solution 1 for GlobalTheory.existsUnique_linearEquiv_lift_of_countable_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:16:10.518423+00:00
-- url     : https://prove2.me/submissions/a4486d36-a28b-47e4-9fe3-2fc87edaff3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Theorems.Thm_GlobalTheory_realLinear_injective_of_countable_ker
import Theorems.Thm_GlobalTheory_realLinear_surjective_of_mod_countable
import Theorems.Thm_GlobalTheory_existsUnique_linear_lift_of_germ
import Theorems.Thm_GlobalTheory_countable_of_isDiscrete_finiteDimensional

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
theorem _root_.solution
    [FiniteDimensional ℝ W] {ex : V →+ A} {ex' : W →+ A} (hc : (ex.ker : Set V).Countable)
    (hk' : IsDiscrete (ex'.ker : Set W)) (hr : ex'.range ≤ ex.range) {g : V → W}
    (hd : DifferentiableAt 𝕜 g 0) (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) :
    ∃! L : V ≃L[𝕜] W, (∀ z, ex' (L z) = ex z) ∧ ex.ker.map (L : V →+ W) = ex'.ker := by
  obtain ⟨L, hL, hu⟩ := existsUnique_linear_lift_of_germ hk' hd hg
  have hc' := countable_of_isDiscrete_finiteDimensional hk'
  have hi : Function.Injective L :=
    realLinear_injective_of_countable_ker (L.restrictScalars ℝ).toLinearMap <|
      hc.mono fun x (hx : L x = 0) ↦ by simp [← hL x, hx]
  have hs : Function.Surjective L :=
    realLinear_surjective_of_mod_countable (L.restrictScalars ℝ).toLinearMap hc' fun y ↦ by
      obtain ⟨x, hx⟩ := hr ⟨y, rfl⟩
      exact ⟨x, by simp [hL, hx]⟩
  let e : V ≃ₗ[𝕜] W := LinearEquiv.ofBijective L.toLinearMap ⟨hi, hs⟩
  have he : Continuous e.symm :=
    (e.restrictScalars ℝ).symm.toLinearMap.continuous_of_finiteDimensional
  refine ⟨⟨e, L.continuous, he⟩, ⟨hL, ?_⟩, fun L' h' ↦ ?_⟩
  · ext y
    obtain ⟨x, rfl⟩ := hs y
    rw [AddMonoidHom.mem_ker, hL]
    exact AddSubgroup.mem_map_iff_mem (f := (L : V →+ W)) hi
  · have := hu (L' : V →L[𝕜] W) h'.1
    ext z
    exact DFunLike.congr_fun this z
end GlobalTheory
