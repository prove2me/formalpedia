-- Prove2me | solution 1 for GlobalTheory.exists_addEquiv_of_linearEquiv_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:45:34.33273+00:00
-- url     : https://prove2.me/submissions/b68b7ef3-068b-45c6-b72a-b572e6034d49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearLiftOfIsMonHomPolAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLatticeAutOfIsomorphicThetaObjects
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {La : Type} [AddCommGroup La] {g : ℕ} (Q Q' : La →+ (Fin g → ℂ))
    (hQ : Function.Injective Q) (hQ' : Function.Injective Q') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (h₁ : ∀ x, h (Q' x) ∈ Q.range) (h₂ : ∀ x, h.symm (Q x) ∈ Q'.range) :
    ∃ gam : La ≃+ La, ∀ x, h (Q' x) = Q (gam x) := by
  choose a ha using h₁
  choose c hc using h₂
  refine ⟨{ toFun := a, invFun := c, left_inv := fun x => hQ' ?_, right_inv := fun x => hQ ?_,
            map_add' := fun x y => hQ ?_ }, fun x => (ha x).symm⟩
  · rw [hc, ha, h.symm_apply_apply]
  · rw [ha, hc, h.apply_symm_apply]
  · rw [map_add, ha, ha, ha, map_add, map_add]
end GlobalTheory
