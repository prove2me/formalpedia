-- Prove2me | solution 1 for GlobalTheory.isPrincipal_of_isStablyFree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:04:58.921856+00:00
-- url     : https://prove2.me/submissions/0d7304fa-390e-4ed6-86d0-f858b54192b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsPrincipalMapAwayOfHasProjectiveDimensionLE
import Theorems.Thm_GlobalTheory_exists_surjective_exteriorPower_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open scoped TensorProduct
namespace GlobalTheory
theorem _root_.solution {A : Type} [CommRing A] (J : Ideal A) [Module.Finite A J]
    [Module.IsStablyFree A J] : J.IsPrincipal := by
  rcases subsingleton_or_nontrivial A with _ | _
  · rw [Subsingleton.elim J ⊥]
    exact bot_isPrincipal
  obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod A J
  let n := Module.finrank A N
  have hp : Module.finrank A (J × N) ≤ n + 1 := by
    have := LinearMap.finrank_le_finrank_of_injective
      (f := J.subtype.prodMap (LinearMap.id : N →ₗ[A] N))
      (Function.Injective.prodMap J.injective_subtype Function.injective_id)
    rwa [Module.finrank_prod (M := A), Module.finrank_self, add_comm] at this
  have h1 : Module.finrank A (⋀[A]^(n + 1) (J × N)) ≤ 1 := by
    rw [exteriorPower.finrank_eq]
    simpa using Nat.choose_le_choose (n + 1) hp
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h1
  obtain ⟨φ, hφ⟩ := exists_surjective_exteriorPower_prod (M := J) (Module.finBasis A N)
  refine ⟨(φ v : A), le_antisymm (fun y hy ↦ ?_) ?_⟩
  · obtain ⟨w, hw⟩ := hφ ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := hv w
    rw [map_smul] at hw
    exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hw⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact (φ v).2
end GlobalTheory
