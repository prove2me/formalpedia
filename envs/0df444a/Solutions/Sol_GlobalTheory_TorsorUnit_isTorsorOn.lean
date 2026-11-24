-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.isTorsorOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:47:12.545334+00:00
-- url     : https://prove2.me/submissions/604ccbec-547d-4f72-851a-30a0c57e9b0e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_GlobalTheory_TorsorUnit_pt_comp
import Theorems.Thm_GlobalTheory_TorsorUnit_pt_injective
import Theorems.Thm_GlobalTheory_TorsorUnit_act_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorsorUnit
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G}
open SplitTorusPoints
namespace GlobalTheory.TorsorUnit
theorem _root_.solution [IsMonHom q] [IsMonHom i] (hi : IsPullback i (toUnit _) q η[B])
    {V : B.left.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen (q.left ⁻¹ᵁ V))
    {ρ : Γ(G.left, q.left ⁻¹ᵁ V) →+* AddMonoidAlgebra Γ(G.left, q.left ⁻¹ᵁ V) X}
    (hρ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (θ), g.left = pt hU θ →
        ((t ≫ i) * g).left = pt hU ((ev θ (toHom t)).comp ρ)) (Z : Scheme.{0}) :
    IsTorsorOn Γ(Z, ⊤) (q.left.appLE V _ le_rfl).hom ρ := by
  let FinalForm : (Γ(G.left, q.left ⁻¹ᵁ V) →+* Γ(Z, ⊤)) → Over S := fun θ => Over.mk (pt hU θ ≫ G.hom)
  let g : ∀ θ, FinalForm θ ⟶ G := fun θ => Over.homMk (pt hU θ) rfl
  have ex : ∀ θ (φ : Multiplicative X →* Γ(Z, ⊤)ˣ), ∃ t : FinalForm θ ⟶ splitTorus S X, toHom t = φ :=
    fun θ φ => (toHom_bijective (Z := FinalForm θ) (X := X)).2 φ
  refine ⟨fun θ φ φ' => ?_, fun θ φ => ?_, fun θ φ φ' h => ?_, fun θ θ' h => ?_⟩
  · obtain ⟨t, rfl⟩ := ex θ φ
    obtain ⟨t', rfl⟩ := ex θ φ'
    have h1 := hρ _ (t * t') (g θ) θ rfl
    have h2 := hρ _ t _ _ (hρ _ t' (g θ) θ rfl)
    rw [toHom_mul, MonObj.mul_comp, _root_.mul_assoc, h2] at h1
    exact (pt_injective hU h1).symm
  · obtain ⟨t, rfl⟩ := ex θ φ
    have h1 := congrArg Over.Hom.left (act_comp hi t (g θ))
    rw [Over.comp_left, Over.comp_left, hρ _ t (g θ) θ rfl] at h1
    exact pt_injective hV ((pt_comp hU hV q.left le_rfl _).symm.trans
      (h1.trans (pt_comp hU hV q.left le_rfl _)))
  · obtain ⟨t, rfl⟩ := ex θ φ
    obtain ⟨t', rfl⟩ := ex θ φ'
    have h1 : (t ≫ i) * g θ = (t' ≫ i) * g θ := Over.OverMorphism.ext
      ((hρ _ t (g θ) θ rfl).trans ((congrArg (pt hU) h).trans (hρ _ t' (g θ) θ rfl).symm))
    rw [hi.hom_ext (mul_right_cancel h1) (toUnit_unique _ _)]
  · have h1 : pt hU θ' ≫ q.left = pt hU θ ≫ q.left := by
      rw [pt_comp hU hV q.left le_rfl, pt_comp hU hV q.left le_rfl, h]
    let g' : FinalForm θ ⟶ G := Over.homMk (pt hU θ') (by
      change _ = pt hU θ ≫ G.hom
      rw [← Over.w q, ← Category.assoc, h1, Category.assoc])
    have h2 : g' ≫ q = g θ ≫ q := Over.OverMorphism.ext h1
    have h3 : (g' * (g θ)⁻¹) ≫ q = toUnit _ ≫ η[B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, h2, mul_inv_cancel, Hom.one_def]
    refine ⟨toHom (hi.lift _ _ h3), pt_injective hU ?_⟩
    refine Eq.trans ?_ (hρ _ (hi.lift _ _ h3) (g θ) θ rfl)
    rw [hi.lift_fst, inv_mul_cancel_right]
    rfl
end GlobalTheory.TorsorUnit
