-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_algHom_isTangentCoordsOfPairAt_regluing_of_local_lift_factor_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c54aa679-4122-508a-ade7-9415436b6c1f

import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat
import Theorems.Thm_GoodReductionJacobian_BareDeformation_isTangentCoordsOfPairAt_comp_regluing_chart_of_comp_incl_bare
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

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_algHom_isTangentCoordsOfPairAt_regluing_of_local_lift_factor_bare

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

theorem solution
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing B₁] [Algebra B B₁]
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f] (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι)

    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))

    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation f₁ L₁ B)
    (ιD : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hιg : ∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιD i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g)
    (hιglue : ∀ s : 𝒰.Idx 1,
      D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ιD (s.1 0) = (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ιD (s.1 1))

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf : ∀ i, m i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)

    (t : 𝒰.Idx 1) (j : 𝒰.ι) (Wo : D₀.A.Opens) (hWo : IsAffineOpen Wo) (hWj : Wo ≤ 𝒰.U j)
    (P : (↑Wo : Scheme.{0}) ⟶ ↑(𝒰.inter t)) (hP : P ≫ (𝒰.inter t).ι = D₀.A.homOfLE hWj ≫ m j)
    (cs : letI := algebraOfHom D₀.f (𝒰.inter t)
      Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t))))
    (hcs : letI := algebraOfHom D₀.f (𝒰.inter t)
      AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter t)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t).fromSpec)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t).isoSpec.inv ≫ (τ t).hom ≫ (𝒰.inter t).ι)
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs) :
    letI := algebraOfHom D₀.f (𝒰.inter t)
    letI := algebraOfHom D₀.f Wo
    ∃ θ : Γ(D₀.A, 𝒰.inter t) →ₐ[B] Γ(D₀.A, Wo),
      Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t).isoSpec.inv = hWo.isoSpec.inv ≫ P ∧
      AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, Wo)
        (hWo.isoSpec.inv ≫ P ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ ιD (t.1 1))
        (hWo.isoSpec.inv ≫ P ≫ D₀.A.homOfLE (𝒰.inter_le t 0) ≫ ιD (t.1 0))
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) θ).toLinearMap ∘ₗ cs a) := by

  letI instT : Algebra B Γ(D₀.A, 𝒰.inter t) := algebraOfHom D₀.f (𝒰.inter t)
  letI instW : Algebra B Γ(D₀.A, Wo) := algebraOfHom D₀.f Wo
  have hUt : IsAffineOpen (𝒰.inter t) := Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t

  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(D₀.A, 𝒰.inter t) ⟶ Γ(D₀.A, Wo),
      Spec.map φ = hWo.isoSpec.inv ≫ P ≫ hUt.isoSpec.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩

  have hPf : P ≫ (𝒰.inter t).ι ≫ D₀.f = Wo.ι ≫ D₀.f := by
    rw [← Category.assoc, hP, Category.assoc, hmf, ← Category.assoc, Scheme.homOfLE_ι]
  have hres : P ≫ D₀.f.resLE ⊤ (𝒰.inter t) le_top = D₀.f.resLE ⊤ Wo le_top := by
    rw [← cancel_mono (⊤ : (Spec (CommRingCat.of B)).Opens).ι, Category.assoc,
      Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι, hPf]
  have hspec : ∀ (U : D₀.A.Opens) (hU : IsAffineOpen U),
      Spec.map (D₀.f.appLE ⊤ U le_top) =
        hU.isoSpec.inv ≫ D₀.f.resLE ⊤ U le_top ≫ (⊤ : (Spec (CommRingCat.of B)).Opens).toSpecΓ := by
    intro U hU
    rw [← cancel_epi hU.isoSpec.hom, Iso.hom_inv_id_assoc, IsAffineOpen.isoSpec_hom,
      Scheme.Opens.toSpecΓ_SpecMap_appLE]
  have hcomm : D₀.f.appLE ⊤ (𝒰.inter t) le_top ≫ φ = D₀.f.appLE ⊤ Wo le_top := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hspec _ hUt, hspec _ hWo]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← hres, Category.assoc]

  let θ : Γ(D₀.A, 𝒰.inter t) →ₐ[B] Γ(D₀.A, Wo) :=
    { φ.hom with
      commutes' := fun b => by
        change (((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ D₀.f.appLE ⊤ (𝒰.inter t) le_top) ≫ φ).hom b =
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ D₀.f.appLE ⊤ Wo le_top).hom b
        rw [Category.assoc, hcomm] }
  have hθφ : CommRingCat.ofHom θ.toRingHom = φ := CommRingCat.hom_ext (RingHom.ext fun _ => rfl)

  haveI hflat : Module.Flat B Γ(D₀.A, Wo) := by
    have h : (algebraMap B Γ(D₀.A, Wo)).Flat := by
      change ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ D₀.f.appLE ⊤ Wo le_top).hom.Flat
      rw [CommRingCat.hom_comp]
      refine RingHom.Flat.comp ?_ ?_
      · exact RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of B)).symm.commRingCatIsoToRingEquiv.bijective
      · haveI : Smooth D₀.f := D₀.bundle.smooth
        exact HasRingHomProperty.appLE @Flat D₀.f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨Wo, hWo⟩ le_top
    exact RingHom.flat_algebraMap_iff.mp h

  have h1 := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat
    (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒰.inter t) Γ(D₀.A, Wo) θ
    hUt.fromSpec (hUt.isoSpec.inv ≫ (τ t).hom ≫ (𝒰.inter t).ι)
    (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
    (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs hcs
  have hu : Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ hUt.fromSpec =
      (hWo.isoSpec.inv ≫ P ≫ D₀.A.homOfLE (𝒰.inter_le t 1)) ≫ (𝒰.U (t.1 1)).ι := by
    rw [hθφ, hφ, ← IsAffineOpen.isoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]
  have hv : Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ hUt.isoSpec.inv ≫ (τ t).hom ≫ (𝒰.inter t).ι =
      (hWo.isoSpec.inv ≫ P ≫ (τ t).hom ≫ D₀.A.homOfLE (𝒰.inter_le t 1)) ≫ (𝒰.U (t.1 1)).ι := by
    rw [hθφ, hφ]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]
  rw [hu, hv] at h1

  have h2 := GoodReductionJacobian.BareDeformation.isTangentCoordsOfPairAt_comp_regluing_chart_of_comp_incl_bare
    B B₁ hsmall f₁ L₁ hI V ι D₀ 𝒰 i₀ jκ hjκ D (t.1 1) (ιD (t.1 1)) (hιg (t.1 1)) Γ(D₀.A, Wo)
    (hWo.isoSpec.inv ≫ P ≫ D₀.A.homOfLE (𝒰.inter_le t 1))
    (hWo.isoSpec.inv ≫ P ≫ (τ t).hom ≫ D₀.A.homOfLE (𝒰.inter_le t 1)) _ h1
  refine ⟨θ, ?_, ?_⟩
  · rw [hθφ, hφ]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · simpa only [Category.assoc, ← hιglue t] using h2

end S_GoodReductionJacobian_BareDeformation_exists_algHom_isTangentCoordsOfPairAt_regluing_of_local_lift_factor_bare
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_algHom_isTangentCoordsOfPairAt_regluing_of_local_lift_factor_bare (solution)
