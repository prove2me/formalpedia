-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_equiv_schemeHomOver_withConv_algHom_of_isAffineHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f3f658c3-2eb3-58bc-9efa-eb88e4f22874

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_schemeHomOver_withConv_algHom_of_isAffineHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian

namespace S17SC1

noncomputable def toAff {U X : Scheme.{0}} [IsAffine X] (y : U ⟶ X) : Spec Γ(U, ⊤) ⟶ X :=
  Spec.map y.appTop ≫ X.isoSpec.inv

theorem toSpecΓ_toAff {U X : Scheme.{0}} [IsAffine X] (y : U ⟶ X) : U.toSpecΓ ≫ toAff y = y := by
  unfold toAff
  rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

theorem toAff_injective {U X : Scheme.{0}} [IsAffine X] {z₁ z₂ : Spec Γ(U, ⊤) ⟶ X}
    (h : U.toSpecΓ ≫ z₁ = U.toSpecΓ ≫ z₂) : z₁ = z₂ := by
  apply ext_of_isAffine
  have h1 := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h1
  exact (cancel_mono _).1 h1

theorem toAff_unique {U X : Scheme.{0}} [IsAffine X] (y : U ⟶ X) (z : Spec Γ(U, ⊤) ⟶ X)
    (hz : U.toSpecΓ ≫ z = y) : z = toAff y :=
  toAff_injective (hz.trans (toSpecΓ_toAff y).symm)

theorem toAff_comp {U V X : Scheme.{0}} [IsAffine X] (ψ : V ⟶ U) (y : U ⟶ X) :
    toAff (ψ ≫ y) = Spec.map ψ.appTop ≫ toAff y := by
  symm
  apply toAff_unique
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_toAff]

noncomputable def overEquiv {X : Scheme.{0}} (gX : X ⟶ Spec (CommRingCat.of ℤ)) [IsAffine X]
    (U : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)) :
    SchemeHomOver u gX ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ Γ(U, ⊤)))) gX where
  toFun y := ⟨toAff y.1, specZIsTerminal.hom_ext _ _⟩
  invFun z := GoodReductionJacobian.schemeHomOverComp U.toSpecΓ (specZIsTerminal.hom_ext _ _) z
  left_inv y := Subtype.ext (toSpecΓ_toAff y.1)
  right_inv _ := Subtype.ext (toAff_unique _ _ rfl).symm

theorem overEquiv_apply_coe {X : Scheme.{0}} (gX : X ⟶ Spec (CommRingCat.of ℤ)) [IsAffine X]
    (U : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)) (y : SchemeHomOver u gX) :
    (overEquiv gX U u y).1 = toAff y.1 := rfl

end S17SC1

open S17SC1 in

theorem solution
    {X : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of ℤ)} (LX : RelativeGroupLaw ℤ gX) [IsAffineHom gX]
    (H : Type) [CommRing H] [HopfAlgebra ℤ H]
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) gX)
    (hePts_mul : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H →ₐ[ℤ] T)),
      ePts T (φ * ψ) = LX.mul _ (ePts T φ) (ePts T ψ))
    (hePts_nat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
        (σ : T →ₐ[ℤ] T') (φ : WithConv (H →ₐ[ℤ] T)),
      (ePts T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts T φ).1) :
    ∃ eU : ∀ (U : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)), SchemeHomOver u gX ≃ WithConv (H →ₐ[ℤ] Γ(U, ⊤)),

      (∀ (U : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)) (y : SchemeHomOver u gX),
        y.1 = U.toSpecΓ ≫ (ePts Γ(U, ⊤) (eU U u y)).1) ∧

      (∀ (U : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)) (y y' : SchemeHomOver u gX),
        eU U u (LX.mul u y y') = eU U u y * eU U u y') ∧

      (∀ (U V : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)) (v : V ⟶ Spec (CommRingCat.of ℤ)) (ψ : V ⟶ U)
          (hψ : ψ ≫ u = v) (y : SchemeHomOver u gX) (h : H),
        (eU V v (GoodReductionJacobian.schemeHomOverComp ψ hψ y)).ofConv h = (Scheme.Γ.map ψ.op) ((eU U u y).ofConv h)) := by

  haveI : IsAffine X := isAffine_of_isAffineHom gX
  refine ⟨fun U u => (overEquiv gX U u).trans (ePts Γ(U, ⊤)).symm, ?_, ?_, ?_⟩
  ·
    intro U u y
    rw [Equiv.trans_apply, Equiv.apply_symm_apply, overEquiv_apply_coe, toSpecΓ_toAff]
  ·
    intro U u y y'
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply]
    apply (ePts Γ(U, ⊤)).injective
    rw [hePts_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hψ : U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ Γ(U, ⊤))) = u :=
      specZIsTerminal.hom_ext _ _
    have hy : GoodReductionJacobian.schemeHomOverComp U.toSpecΓ hψ (overEquiv gX U u y) = y :=
      Subtype.ext (toSpecΓ_toAff y.1)
    have hy' : GoodReductionJacobian.schemeHomOverComp U.toSpecΓ hψ (overEquiv gX U u y') = y' :=
      Subtype.ext (toSpecΓ_toAff y'.1)
    have hnat := LX.mul_natural _ u U.toSpecΓ hψ (overEquiv gX U u y) (overEquiv gX U u y')
    rw [hy, hy'] at hnat
    apply Subtype.ext
    rw [overEquiv_apply_coe]
    symm
    apply toAff_unique
    rw [← hnat, GoodReductionJacobian.schemeHomOverComp_coe]
  ·
    intro U V u v ψ hψ y h
    rw [Equiv.trans_apply, Equiv.trans_apply]
    let σ : Γ(U, ⊤) →ₐ[ℤ] Γ(V, ⊤) := (ψ.appTop).hom.toIntAlgHom
    have key : (ePts Γ(V, ⊤)).symm (overEquiv gX V v (GoodReductionJacobian.schemeHomOverComp ψ hψ y)) =
        .toConv (σ.comp ((ePts Γ(U, ⊤)).symm (overEquiv gX U u y)).ofConv) := by
      apply (ePts Γ(V, ⊤)).injective
      apply Subtype.ext
      rw [Equiv.apply_symm_apply, hePts_nat, Equiv.apply_symm_apply, overEquiv_apply_coe,
        overEquiv_apply_coe, GoodReductionJacobian.schemeHomOverComp_coe, toAff_comp]
      rfl
    rw [key, WithConv.ofConv_toConv, AlgHom.comp_apply]
    show (ψ.appTop).hom _ = _
    rfl

end S_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_schemeHomOver_withConv_algHom_of_isAffineHom
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_schemeHomOver_withConv_algHom_of_isAffineHom (solution)
