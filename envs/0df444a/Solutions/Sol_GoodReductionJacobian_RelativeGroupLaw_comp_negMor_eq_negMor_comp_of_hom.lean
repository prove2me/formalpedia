-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/178f4739-8ec7-5d2b-b379-dace51a58318

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_hom

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace B1NegmorHom

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (G : RelativeGroupLaw R f)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t'
  have h : schemeHomOverComp ψ hψ (G.inv t x) * schemeHomOverComp ψ hψ x = 1 := by
    show G.mul t' _ _ = G.one t'
    rw [← G.mul_natural t t' ψ hψ, G.inv_mul_cancel, G.one_natural t t' ψ hψ]
  have h' : G.inv t' (schemeHomOverComp ψ hψ x) * schemeHomOverComp ψ hψ x = 1 :=
    G.inv_mul_cancel t' _
  exact mul_right_cancel (h.trans h'.symm)

end B1NegmorHom

open B1NegmorHom in
theorem solution
    {S₁ S₂ : Type} [CommRing S₁] [CommRing S₂] (φ : S₁ →+* S₂)
    {A₁ A₂ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} {f₂ : A₂ ⟶ Spec (CommRingCat.of S₂)}
    (L₁ : RelativeGroupLaw S₁ f₁) (L₂ : RelativeGroupLaw S₂ f₂)
    (v : A₂ ⟶ A₁) (hv : v ≫ f₁ = f₂ ≫ Spec.map (CommRingCat.ofHom φ))
    (hom : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S₂)) (P Q : SchemeHomOver t f₂),
      (L₂.mul t P Q).1 ≫ v =
        (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ v, by rw [Category.assoc, hv, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ v, by rw [Category.assoc, hv, ← Category.assoc, Q.2]⟩).1) :
    v ≫ negMor f₁ L₁ = negMor f₂ L₂ ≫ v := by

  set t₁ : A₂ ⟶ Spec (CommRingCat.of S₁) := f₂ ≫ Spec.map (CommRingCat.ofHom φ) with ht₁

  let vmap : SchemeHomOver f₂ f₂ → SchemeHomOver t₁ f₁ := fun P =>
    ⟨P.1 ≫ v, by rw [Category.assoc, hv, ← Category.assoc, P.2]⟩
  have hmul : ∀ P Q, vmap (L₂.mul f₂ P Q) = L₁.mul t₁ (vmap P) (vmap Q) := fun P Q =>
    Subtype.ext (hom A₂ f₂ P Q)
  letI G₂ := L₂.pointGroup f₂
  letI G₁ := L₁.pointGroup t₁
  have hone : vmap (L₂.one f₂) = L₁.one t₁ := by
    have h : vmap (L₂.one f₂) * vmap (L₂.one f₂) = vmap (L₂.one f₂) := by
      show L₁.mul t₁ _ _ = _
      rw [← hmul, L₂.one_mul]
    exact mul_left_cancel (h.trans (mul_one _).symm)
  have hinv : ∀ P, vmap (L₂.inv f₂ P) = L₁.inv t₁ (vmap P) := fun P => by
    have h : vmap (L₂.inv f₂ P) * vmap P = 1 := by
      show L₁.mul t₁ _ _ = L₁.one t₁
      rw [← hmul, L₂.inv_mul_cancel, hone]
    exact eq_inv_of_mul_eq_one_left h

  have hR : negMor f₂ L₂ ≫ v = (L₁.inv t₁ (vmap (idPt f₂))).1 := by
    show (vmap (L₂.inv f₂ (idPt f₂))).1 = _
    rw [hinv]

  have hL : v ≫ negMor f₁ L₁ = (L₁.inv t₁ (schemeHomOverComp v hv (idPt f₁))).1 := by
    show (schemeHomOverComp v hv (L₁.inv f₁ (idPt f₁))).1 = _
    rw [inv_natural L₁ f₁ t₁ v hv]
  rw [hL, hR]
  have hpt : schemeHomOverComp v hv (idPt f₁) = vmap (idPt f₂) :=
    Subtype.ext (show v ≫ (idPt f₁).1 = (idPt f₂).1 ≫ v by simp [idPt])
  rw [hpt]

end S_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_hom
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_hom (solution)
