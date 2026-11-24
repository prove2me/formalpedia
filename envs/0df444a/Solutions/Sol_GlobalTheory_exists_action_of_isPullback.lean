-- Prove2me | solution 1 for GlobalTheory.exists_action_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:46:34.891214+00:00
-- url     : https://prove2.me/submissions/228d7603-8fb9-4ff0-8c39-12c95d42cc91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback

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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Γ : Type} [Group Γ] {X X' Y Y' : Scheme.{0}}
    (ρ : Γ →* Aut X) {π : X ⟶ X'} {φ : Y ⟶ Y'} {p : Y ⟶ X} {p' : Y' ⟶ X'}
    (hπ : ∀ g, (ρ g).hom ≫ π = π) (H : IsPullback p φ π p') :
    ∃ τ : Γ →* Aut Y, ∀ g, (τ g).hom ≫ φ = φ ∧ (τ g).hom ≫ p = p ≫ (ρ g).hom := by
  have hc : ∀ g : Γ, (p ≫ (ρ g).hom) ≫ π = φ ≫ p' := fun g => by
    rw [Category.assoc, hπ g, H.w]
  let e : Γ → (Y ⟶ Y) := fun g => H.lift (p ≫ (ρ g).hom) φ (hc g)
  have e_p : ∀ g, e g ≫ p = p ≫ (ρ g).hom := fun g => H.lift_fst _ _ _
  have e_φ : ∀ g, e g ≫ φ = φ := fun g => H.lift_snd _ _ _
  have e_one : e 1 = 𝟙 Y := H.hom_ext
    (by rw [e_p, map_one]; exact (Category.comp_id p).trans (Category.id_comp p).symm)
    (by rw [e_φ, Category.id_comp])
  have e_mul : ∀ g h, e (g * h) = e h ≫ e g := fun g h => H.hom_ext
    (by
      rw [e_p, Category.assoc, e_p, ← Category.assoc, e_p, Category.assoc, map_mul]
      rfl)
    (by rw [e_φ, Category.assoc, e_φ, e_φ])
  let τf : Γ → Aut Y := fun g =>
    { hom := e g
      inv := e g⁻¹
      hom_inv_id := by rw [← e_mul, inv_mul_cancel, e_one]
      inv_hom_id := by rw [← e_mul, mul_inv_cancel, e_one] }
  refine ⟨{ toFun := τf, map_one' := ?_, map_mul' := ?_ }, fun g => ⟨e_φ g, e_p g⟩⟩
  · exact Iso.ext e_one
  · intro g h
    exact Iso.ext (e_mul g h)
end GlobalTheory
