-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_bialgHom_of_schemeHomOver_of_forall_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/02eb4e8e-a355-50a2-a513-679dcb61cacf

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_of_schemeHomOver_of_forall_mul

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_of_schemeHomOver_of_forall_mul.GoodReductionJacobian"

universe u

namespace GoodReductionJacobian p2m_export "GoodReductionJacobian" "RelativeGroupLaw" namespace RelativeGroupLaw p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_one one inv one_mul mul" end GoodReductionJacobian.RelativeGroupLaw
p2m_open_scoped "GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw" in

theorem GoodReductionJacobian.RelativeGroupLaw.exists_bialgHom_of_schemeHomOver_of_forall_mul'
    {R : Type u} [CommRing R]
    {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R g) [IsAffineHom g]
    {A' : Scheme.{u}} {g' : A' ⟶ Spec (CommRingCat.of R)} (L' : RelativeGroupLaw R g') [IsAffineHom g']
    (u : SchemeHomOver g' g)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g'),
      (⟨(L'.mul t x y).1 ≫ u.1, by rw [Category.assoc, u.2, (L'.mul t x y).2]⟩ : SchemeHomOver t g) =
        L.mul t ⟨x.1 ≫ u.1, by rw [Category.assoc, u.2, x.2]⟩ ⟨y.1 ≫ u.1, by rw [Category.assoc, u.2, y.2]⟩)
    (H : Type u) [CommRing H] [HopfAlgebra R H] (H' : Type u) [CommRing H'] [HopfAlgebra R H'] :
    letI : Algebra R Γ(A, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.toAlgebra
    letI : Algebra R Γ(A', ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g'.appTop).hom.toAlgebra
    haveI : IsAffine A := isAffine_of_isAffineHom g
    haveI : IsAffine A' := isAffine_of_isAffineHom g'
    ∀ (iso : H ≃ₐ[R] Γ(A, ⊤)) (iso' : H' ≃ₐ[R] Γ(A', ⊤))
      (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (H →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) g)
      (e' : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (H' →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) g'),
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
        (e T φ).1 = Spec.map (CommRingCat.ofHom ((φ.ofConv.comp (iso.symm : Γ(A, ⊤) →ₐ[R] H)).toRingHom)) ≫ A.isoSpec.inv) →
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H' →ₐ[R] T)),
        (e' T φ).1 = Spec.map (CommRingCat.ofHom ((φ.ofConv.comp (iso'.symm : Γ(A', ⊤) →ₐ[R] H')).toRingHom)) ≫ A'.isoSpec.inv) →
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)), e T (φ * ψ) = L.mul _ (e T φ) (e T ψ)) →
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H' →ₐ[R] T)), e' T (φ * ψ) = L'.mul _ (e' T φ) (e' T ψ)) →
      ∃ ψ : H →ₐc[R] H',
        (∀ h : H, iso' (ψ h) = u.1.appTop.hom (iso h)) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ' : WithConv (H' →ₐ[R] T)),
          (e T (.toConv (φ'.ofConv.comp (ψ : H →ₐ[R] H')))).1 = (e' T φ').1 ≫ u.1) ∧
        (IsClosedImmersion u.1 → Function.Surjective ψ) := by
  intro iso iso' e e' he he' hmul hmul'
  letI : Algebra R Γ(A, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.toAlgebra
  letI : Algebra R Γ(A', ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g'.appTop).hom.toAlgebra
  haveI : IsAffine A := isAffine_of_isAffineHom g
  haveI : IsAffine A' := isAffine_of_isAffineHom g'

  have hΓ : g.appTop ≫ u.1.appTop = g'.appTop := by
    have h2 : (u.1 ≫ g).appTop = g'.appTop := congrArg Scheme.Hom.appTop u.2
    exact h2
  let Γu : Γ(A, ⊤) →ₐ[R] Γ(A', ⊤) :=
    { u.1.appTop.hom with
      commutes' := fun r => by
        show u.1.appTop.hom (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom r) =
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g'.appTop).hom r
        rw [← hΓ]; rfl }
  let ψₐ : H →ₐ[R] H' := (iso'.symm : Γ(A', ⊤) →ₐ[R] H').comp (Γu.comp (iso : H →ₐ[R] Γ(A, ⊤)))
  have hψ1 : ∀ h : H, iso' (ψₐ h) = u.1.appTop.hom (iso h) := fun h => by
    simp [ψₐ, Γu]

  have hψ2 : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ' : WithConv (H' →ₐ[R] T)),
      (e T (.toConv (φ'.ofConv.comp ψₐ))).1 = (e' T φ').1 ≫ u.1 := by
    intro T _ _ φ'
    rw [he, he', Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    ext a
    show (φ'.ofConv.comp ψₐ) (iso.symm a) = φ'.ofConv (iso'.symm (u.1.appTop.hom a))
    simp [ψₐ, Γu]

  have hY1 : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ' : WithConv (H' →ₐ[R] T)),
      e T (.toConv (φ'.ofConv.comp ψₐ)) =
        ⟨(e' T φ').1 ≫ u.1, by rw [Category.assoc, u.2, (e' T φ').2]⟩ :=
    fun T _ _ φ' => Subtype.ext (hψ2 T φ')

  have hone : ∀ (T : Type u) [CommRing T] [Algebra R T], e T 1 = L.one _ := by
    intro T _ _
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R T)))
    have h := hmul T 1 1
    rw [_root_.mul_one] at h
    exact mul_eq_right.mp (h.symm : (e T 1 * e T 1 : SchemeHomOver _ g) = e T 1)
  have hone' : ∀ (T : Type u) [CommRing T] [Algebra R T], e' T 1 = L'.one _ := by
    intro T _ _
    letI := L'.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R T)))
    have h := hmul' T 1 1
    rw [_root_.mul_one] at h
    exact mul_eq_right.mp (h.symm : (e' T 1 * e' T 1 : SchemeHomOver _ g') = e' T 1)

  have huone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      (⟨(L'.one t).1 ≫ u.1, by rw [Category.assoc, u.2, (L'.one t).2]⟩ : SchemeHomOver t g) = L.one t := by
    intro T t
    letI := L.pointGroup t
    have h := hu t (L'.one t) (L'.one t)
    simp only [L'.one_mul] at h
    exact mul_eq_right.mp (h.symm : (_ * _ : SchemeHomOver t g) = _)

  have hcounit : (Bialgebra.counitAlgHom R H').comp ψₐ = Bialgebra.counitAlgHom R H := by
    have h1 : ∀ (K : Type u) [CommRing K] [HopfAlgebra R K],
        (1 : WithConv (K →ₐ[R] R)) = .toConv (Bialgebra.counitAlgHom R K) := by
      intro K _ _
      rw [AlgHom.convOne_def]
      congr 1
    apply WithConv.toConv_injective
    apply (e R).injective
    rw [hY1, ← h1 H, hone R]
    have : e' R (.toConv (Bialgebra.counitAlgHom R H')) = L'.one _ := by rw [← h1 H', hone' R]
    simp only [this]
    exact huone _
  have hcomul : (Algebra.TensorProduct.map ψₐ ψₐ).comp (Bialgebra.comulAlgHom R H) =
      (Bialgebra.comulAlgHom R H').comp ψₐ := by
    let T : Type u := TensorProduct R H' H'
    let ι₁ : H' →ₐ[R] T := Algebra.TensorProduct.includeLeft
    let ι₂ : H' →ₐ[R] T := Algebra.TensorProduct.includeRight

    have hid : (Algebra.TensorProduct.lmul' R (S := T)).comp (Algebra.TensorProduct.map ι₁ ι₂) = AlgHom.id R T := by
      ext a
      all_goals (simp [ι₁, ι₂]; try rfl)

    have hF1 : (WithConv.toConv ι₁ * WithConv.toConv ι₂ : WithConv (H' →ₐ[R] T)).ofConv = Bialgebra.comulAlgHom R H' := by
      rw [AlgHom.convMul_def, WithConv.ofConv_toConv, ← AlgHom.comp_assoc, hid, AlgHom.id_comp]

    have hF2 : (WithConv.toConv (ι₁.comp ψₐ) * WithConv.toConv (ι₂.comp ψₐ) : WithConv (H →ₐ[R] T)).ofConv =
        (Algebra.TensorProduct.map ψₐ ψₐ).comp (Bialgebra.comulAlgHom R H) := by
      rw [AlgHom.convMul_def, WithConv.ofConv_toConv, Algebra.TensorProduct.map_comp, ← AlgHom.comp_assoc,
        ← AlgHom.comp_assoc, hid, AlgHom.id_comp]

    apply WithConv.toConv_injective
    apply (e T).injective
    have lhs : e T (.toConv ((Algebra.TensorProduct.map ψₐ ψₐ).comp (Bialgebra.comulAlgHom R H))) =
        L.mul _ (e T (.toConv (ι₁.comp ψₐ))) (e T (.toConv (ι₂.comp ψₐ))) := by
      rw [← hF2, WithConv.toConv_ofConv, hmul]
    have rhs : e T (.toConv ((Bialgebra.comulAlgHom R H').comp ψₐ)) =
        L.mul _ (e T (.toConv (ι₁.comp ψₐ))) (e T (.toConv (ι₂.comp ψₐ))) := by
      rw [← hF1, hY1, hY1, hY1, hmul', ← hu]
    rw [lhs, rhs]
  refine ⟨BialgHom.ofAlgHom ψₐ hcounit hcomul, hψ1, hψ2, ?_⟩

  intro hci
  have hsurj : Function.Surjective u.1.appTop := (IsClosedImmersion.isAffine_surjective_of_isAffine u.1).2
  intro h'
  obtain ⟨a, ha⟩ := hsurj (iso' h')
  refine ⟨iso.symm a, ?_⟩
  apply iso'.injective
  show iso' (ψₐ (iso.symm a)) = iso' h'
  rw [hψ1, AlgEquiv.apply_symm_apply, ← ha]

theorem solution
    {R : Type u} [CommRing R]
    {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R g) [IsAffineHom g]
    {A' : Scheme.{u}} {g' : A' ⟶ Spec (CommRingCat.of R)} (L' : RelativeGroupLaw R g') [IsAffineHom g']
    (u : SchemeHomOver g' g)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g'),
      (⟨(L'.mul t x y).1 ≫ u.1, by rw [Category.assoc, u.2, (L'.mul t x y).2]⟩ : SchemeHomOver t g) =
        L.mul t ⟨x.1 ≫ u.1, by rw [Category.assoc, u.2, x.2]⟩ ⟨y.1 ≫ u.1, by rw [Category.assoc, u.2, y.2]⟩)
    (H : Type u) [CommRing H] [HopfAlgebra R H] (H' : Type u) [CommRing H'] [HopfAlgebra R H'] :
    letI : Algebra R Γ(A, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.toAlgebra
    letI : Algebra R Γ(A', ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g'.appTop).hom.toAlgebra
    haveI : IsAffine A := isAffine_of_isAffineHom g
    haveI : IsAffine A' := isAffine_of_isAffineHom g'
    ∀ (iso : H ≃ₐ[R] Γ(A, ⊤)) (iso' : H' ≃ₐ[R] Γ(A', ⊤))
      (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (H →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) g)
      (e' : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (H' →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) g'),
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
        (e T φ).1 = Spec.map (CommRingCat.ofHom ((φ.ofConv.comp (iso.symm : Γ(A, ⊤) →ₐ[R] H)).toRingHom)) ≫ A.isoSpec.inv) →
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H' →ₐ[R] T)),
        (e' T φ).1 = Spec.map (CommRingCat.ofHom ((φ.ofConv.comp (iso'.symm : Γ(A', ⊤) →ₐ[R] H')).toRingHom)) ≫ A'.isoSpec.inv) →
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)), e T (φ * ψ) = L.mul _ (e T φ) (e T ψ)) →
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H' →ₐ[R] T)), e' T (φ * ψ) = L'.mul _ (e' T φ) (e' T ψ)) →
      ∃ ψ : H →ₐc[R] H',
        (∀ h : H, iso' (ψ h) = u.1.appTop.hom (iso h)) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ' : WithConv (H' →ₐ[R] T)),
          (e T (.toConv (φ'.ofConv.comp (ψ : H →ₐ[R] H')))).1 = (e' T φ').1 ≫ u.1) ∧
        (IsClosedImmersion u.1 → Function.Surjective ψ) :=
  GoodReductionJacobian.RelativeGroupLaw.exists_bialgHom_of_schemeHomOver_of_forall_mul' L L' u hu H H'

end S_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_of_schemeHomOver_of_forall_mul
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_of_schemeHomOver_of_forall_mul (solution)
