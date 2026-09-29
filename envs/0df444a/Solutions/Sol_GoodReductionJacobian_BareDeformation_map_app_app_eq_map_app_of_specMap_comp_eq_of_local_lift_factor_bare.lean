-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.map_app_app_eq_map_app_of_specMap_comp_eq_of_local_lift_factor_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a884434a-d833-5606-8539-bb60f5605774

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_map_app_app_eq_map_app_of_specMap_comp_eq_of_local_lift_factor_bare

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

theorem solution
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f] (𝒰 : D₀.A.OrderedAffineCover)

    (φ₁ : A₁ ⟶ A₁)
    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))
    (ψ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ (pullback D₀.f (specMap B (ResidueField B))))
    (hψ₁ : ψ ≫ jκ = jκ ≫ φ₁)

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D₀.g)

    (j : 𝒰.ι) (W U' : D₀.A.Opens) (hW : IsAffineOpen W) (hU' : IsAffineOpen U') (hWj : W ≤ 𝒰.U j)
    (p : (↑W : Scheme.{0}) ⟶ ↑U') (hp : p ≫ U'.ι = D₀.A.homOfLE hWj ≫ m j)
    (θ : letI := algebraOfHom D₀.f U'
      letI := algebraOfHom D₀.f W
      Γ(D₀.A, U') →ₐ[B] Γ(D₀.A, W))
    (hθ : letI := algebraOfHom D₀.f U'
      letI := algebraOfHom D₀.f W
      Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ hU'.isoSpec.inv = hW.isoSpec.inv ≫ p)

    (W' U'' : (pullback D₀.f (specMap B (ResidueField B))).Opens)
    (e₁ : U'' ≤ (pullback.fst D₀.f (specMap B (ResidueField B))) ⁻¹ᵁ U') (e₂ : W' ≤ ψ ⁻¹ᵁ U'') (e₃ : W' ≤ (pullback.fst D₀.f (specMap B (ResidueField B))) ⁻¹ᵁ W)
    (y : Γ(D₀.A, U')) :
    letI := algebraOfHom D₀.f U'
    letI := algebraOfHom D₀.f W
    ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE e₂).op).hom
        ((ψ.app U'').hom (((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE e₁).op).hom (((pullback.fst D₀.f (specMap B (ResidueField B))).app U').hom y))) =
      ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE e₃).op).hom (((pullback.fst D₀.f (specMap B (ResidueField B))).app W).hom (θ y)) := by
  classical

  have eβ : W' ≤ (ψ ≫ (pullback.fst D₀.f (specMap B (ResidueField B)))) ⁻¹ᵁ U' := by
    rw [Scheme.Hom.comp_preimage]
    exact e₂.trans (Scheme.Hom.preimage_mono ψ e₁)
  have ej : W' ≤ (pullback.fst D₀.f (specMap B (ResidueField B))) ⁻¹ᵁ 𝒰.U j := e₃.trans (Scheme.Hom.preimage_mono _ hWj)
  have elam : W' ≤ jκ ⁻¹ᵁ (D₀.g ⁻¹ᵁ 𝒰.U j) := by
    rw [← Scheme.Hom.comp_preimage, hjκ]; exact ej

  have hsq : (pullback.fst D₀.f (specMap B (ResidueField B))).resLE W W' e₃ ≫ p = (ψ ≫ (pullback.fst D₀.f (specMap B (ResidueField B)))).resLE U' W' eβ := by
    rw [← cancel_mono U'.ι]
    rw [Category.assoc, hp, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_map]

    have hlamj : (pullback.fst D₀.f (specMap B (ResidueField B))).resLE (𝒰.U j) W' ej = jκ.resLE (D₀.g ⁻¹ᵁ 𝒰.U j) W' elam ≫ (D₀.g ∣_ 𝒰.U j) := by
      rw [← cancel_mono (𝒰.U j).ι, Scheme.Hom.resLE_comp_ι, Category.assoc, morphismRestrict_ι,
        Scheme.Hom.resLE_comp_ι_assoc, hjκ]
    rw [hlamj, Category.assoc, hmμ, Scheme.Hom.resLE_comp_ι_assoc, ← hjκ, ← Category.assoc ψ jκ, hψ₁, Category.assoc]

  letI := algebraOfHom D₀.f U'
  letI := algebraOfHom D₀.f W
  have hθ' : ∀ z : Γ(↑U', ⊤), θ (U'.topIso.hom.hom z) = W.topIso.hom.hom (p.appTop.hom z) := by
    intro z
    have h1 := congrArg Scheme.Hom.appTop hθ
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, hU'.isoSpec_inv_appTop, hW.isoSpec_inv_appTop, Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, ← Category.assoc] at h1
    have h1' : U'.topIso.hom ≫ CommRingCat.ofHom θ.toRingHom = p.appTop ≫ W.topIso.hom :=
      (cancel_mono ((Scheme.ΓSpecIso Γ(D₀.A, W)).inv)).mp h1
    have h2 := congrArg (fun f => f.hom z) h1'
    simpa using h2
  have hθy : θ y = W.topIso.hom.hom (p.appTop.hom (U'.topIso.inv.hom y)) := by
    have := hθ' (U'.topIso.inv.hom y)
    rwa [← CommRingCat.comp_apply, Iso.inv_hom_id] at this

  have happLE : ∀ {S T : Scheme.{0}} (h : S ⟶ T) (U : T.Opens) (V : S.Opens) (e : V ≤ h ⁻¹ᵁ U) (z : Γ(T, U)),
      (h.appLE U V e).hom z = V.topIso.hom.hom ((h.resLE U V e).appTop.hom (U.topIso.inv.hom z)) := by
    intro S T h U V e z
    have t1 := Scheme.Hom.resLE_app_top h e
    have t2 : U.topIso.inv ≫ (U.topIso.hom ≫ h.appLE U V e ≫ V.topIso.inv) ≫ V.topIso.hom = h.appLE U V e := by
      rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    conv_lhs => rw [← t2]
    rw [← t1]
    rfl

  change (ψ.appLE U'' W' e₂).hom (((pullback.fst D₀.f (specMap B (ResidueField B))).appLE U' U'' e₁).hom y) = ((pullback.fst D₀.f (specMap B (ResidueField B))).appLE W W' e₃).hom (θ y)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, happLE, happLE, hθy, ← CommRingCat.comp_apply W.topIso.hom,
    Iso.hom_inv_id, CommRingCat.id_apply, ← CommRingCat.comp_apply p.appTop, ← Scheme.Hom.comp_appTop, hsq]

end S_GoodReductionJacobian_BareDeformation_map_app_app_eq_map_app_of_specMap_comp_eq_of_local_lift_factor_bare
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_map_app_app_eq_map_app_of_specMap_comp_eq_of_local_lift_factor_bare (solution)
