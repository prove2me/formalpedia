-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_away_mul_of_symmetric_principalSqrt_faithfullyFlat_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6adb8fb6-bf49-5ee7-8bae-819537d49c5b

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_KernelTrivial_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_IsSymmetric_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_away_mul_of_symmetric_principalSqrt_faithfullyFlat_atPrime
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace NEG22

theorem inv_coe_congr {S : Type} [CommRing S] {A T : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {P₁ : SchemeHomOver t₁ f} {P₂ : SchemeHomOver t₂ f} (hP : P₁.1 = P₂.1) :
    (L.inv t₁ P₁).1 = (L.inv t₂ P₂).1 := by
  subst ht
  rw [Subtype.ext hP]

theorem inv_natural' {S : Type} [CommRing S] {A T T' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t
  letI := L.pointGroup t'
  let F : SchemeHomOver t f →* SchemeHomOver t' f :=
    MonoidHom.mk' (GoodReductionJacobian.schemeHomOverComp ψ hψ) (fun a b => L.mul_natural t t' ψ hψ a b)
  exact map_inv F x

theorem negMor_comp_of_isPullback {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) :
    negMor f' L' ≫ g = g ≫ negMor f L := by
  have hinv : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f'),
      (L'.inv t' P).1 ≫ g =
        (L.inv (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩).1 := by
    intro T t' P
    letI := L'.pointGroup t'
    letI := L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ))
    let F : SchemeHomOver t' f' →* SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f :=
      MonoidHom.mk' (fun P => ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩)
        (fun a b => Subtype.ext (hmul t' a b))
    exact congrArg Subtype.val (map_inv F P)
  have lhs := hinv f' (idPt f')
  have rhs := congrArg Subtype.val (inv_natural' L f (g ≫ f) g rfl (idPt f))
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at rhs
  change (L'.inv f' (idPt f')).1 ≫ g = g ≫ (L.inv f (idPt f)).1
  rw [lhs, rhs]
  apply inv_coe_congr L hg.w.symm
  simp only [idPt, GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp, Category.comp_id]

noncomputable def pullbackSqIso {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (M : A.Modules) :
    (Scheme.Modules.pullback g).obj (M ⊗ (Scheme.Modules.pullback (negMor f L)).obj M) ≅
      (Scheme.Modules.pullback g).obj M ⊗
        (Scheme.Modules.pullback (negMor f' L')).obj ((Scheme.Modules.pullback g).obj M) :=
  Scheme.Modules.pullbackTensorObjIso g _ _ ≪≫
    whiskerLeftIso _ ((Scheme.Modules.pullbackComp g _).app M ≪≫
      (Scheme.Modules.pullbackCongr (negMor_comp_of_isPullback φ hg L L' hmul).symm).app M ≪≫
      ((Scheme.Modules.pullbackComp _ g).app M).symm)

end NEG22

namespace SMK26WR

variable {S : Type} [CommRing S]

theorem disjoint_powers_of_not_mem (𝔭 : Ideal S) [h𝔭 : 𝔭.IsPrime] (r : S) (hr : r ∉ 𝔭) :
    Disjoint ((Submonoid.powers r : Submonoid S) : Set S) (𝔭 : Set S) := by
  rw [Set.disjoint_left]
  rintro x ⟨n, rfl⟩ hx
  exact hr (h𝔭.mem_of_pow_mem n hx)

theorem isPrime_map_away (𝔭 : Ideal S) [h𝔭 : 𝔭.IsPrime] (r : S) (hr : r ∉ 𝔭) :
    (Ideal.map (algebraMap S (Localization.Away r)) 𝔭).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers r) _ 𝔭 h𝔭 (disjoint_powers_of_not_mem 𝔭 r hr)

theorem comap_map_away (𝔭 : Ideal S) [h𝔭 : 𝔭.IsPrime] (r : S) (hr : r ∉ 𝔭) :
    (Ideal.map (algebraMap S (Localization.Away r)) 𝔭).comap (algebraMap S (Localization.Away r)) = 𝔭 :=
  IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers r) _ h𝔭 (disjoint_powers_of_not_mem 𝔭 r hr)

theorem isLocalization_primeCompl_atPrime_map_away (𝔭 : Ideal S) [h𝔭 : 𝔭.IsPrime] (r : S) (hr : r ∉ 𝔭) :
    haveI := isPrime_map_away 𝔭 r hr
    IsLocalization 𝔭.primeCompl (Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away r)) 𝔭)) := by
  haveI := isPrime_map_away 𝔭 r hr
  have h := IsLocalization.isLocalization_atPrime_localization_atPrime (M := Submonoid.powers r)
    (Ideal.map (algebraMap S (Localization.Away r)) 𝔭)
  have hsub : (Ideal.comap (algebraMap S (Localization (Submonoid.powers r))) (Ideal.map (algebraMap S (Localization.Away r)) 𝔭)).primeCompl =
      𝔭.primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff]
    exact not_congr (by rw [comap_map_away 𝔭 r hr])
  rw [IsLocalization.AtPrime, hsub] at h
  exact h

theorem exists_algebra_atPrime_map_faithfullyFlat
    (𝔭 : Ideal S) [h𝔭 : 𝔭.IsPrime] (g₀ : S) (hg₀ : g₀ ∉ 𝔭)
    (ψ : Localization.Away g₀ →+* Localization.AtPrime 𝔭)
    (hψ : ψ.comp (algebraMap S (Localization.Away g₀)) = algebraMap S (Localization.AtPrime 𝔭))
    (W : Type) [CommRing W] [Algebra S W] [Algebra (Localization.AtPrime 𝔭) W]
    [IsScalarTower S (Localization.AtPrime 𝔭) W] (hW : Module.FaithfullyFlat (Localization.AtPrime 𝔭) W) :
    haveI := isPrime_map_away 𝔭 g₀ hg₀
    ∃ (_ : Algebra (Localization.Away g₀) W)
      (_ : Algebra (Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭)) W)
      (_ : IsScalarTower (Localization.Away g₀) (Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭)) W)
      (_ : IsScalarTower S (Localization.Away g₀) W),
      Module.FaithfullyFlat (Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭)) W ∧
      algebraMap (Localization.Away g₀) W = (algebraMap (Localization.AtPrime 𝔭) W).comp ψ := by
  classical
  haveI := isPrime_map_away 𝔭 g₀ hg₀
  haveI := isLocalization_primeCompl_atPrime_map_away 𝔭 g₀ hg₀
  haveI := hW

  obtain ⟨e⟩ : Nonempty (Localization.AtPrime 𝔭 ≃ₐ[S] Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭)) :=
    ⟨IsLocalization.algEquiv 𝔭.primeCompl _ _⟩

  have hψe : ψ = e.symm.toAlgHom.toRingHom.comp
      (algebraMap (Localization.Away g₀) (Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭))) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g₀)
    rw [hψ, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    exact (e.symm.toAlgHom.comp_algebraMap).symm

  letI algX : Algebra (Localization.Away g₀) W := ((algebraMap (Localization.AtPrime 𝔭) W).comp ψ).toAlgebra
  letI algP : Algebra (Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭)) W :=
    ((algebraMap (Localization.AtPrime 𝔭) W).comp e.symm.toAlgHom.toRingHom).toAlgebra
  haveI tXP : IsScalarTower (Localization.Away g₀) (Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭)) W :=
    IsScalarTower.of_algebraMap_eq (R := Localization.Away g₀)
      (S := Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭)) (A := W) (fun x => by
      show algebraMap (Localization.AtPrime 𝔭) W (ψ x) =
        algebraMap (Localization.AtPrime 𝔭) W (e.symm.toAlgHom.toRingHom (algebraMap _ _ x))
      rw [hψe]
      rfl)
  haveI tSX : IsScalarTower S (Localization.Away g₀) W :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := Localization.Away g₀) (A := W) (fun s => by
      show algebraMap S W s = algebraMap (Localization.AtPrime 𝔭) W (ψ (algebraMap S (Localization.Away g₀) s))
      rw [← RingHom.comp_apply ψ, hψ, ← IsScalarTower.algebraMap_apply])

  letI algPp : Algebra (Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭)) (Localization.AtPrime 𝔭) :=
    e.symm.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower (Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭)) (Localization.AtPrime 𝔭) W :=
    IsScalarTower.of_algebraMap_eq (R := Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭))
      (S := Localization.AtPrime 𝔭) (A := W) (fun _ => rfl)
  have elin : Localization.AtPrime 𝔭 ≃ₗ[Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭)]
      Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭) :=
    { e.toRingEquiv.toAddEquiv with
      map_smul' := fun c x => by
        show e (e.symm.toAlgHom.toRingHom c * x) = c * e x
        rw [map_mul]
        exact congrArg (· * e x) (e.apply_symm_apply c) }
  haveI : Module.FaithfullyFlat (Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭)) (Localization.AtPrime 𝔭) :=
    Module.FaithfullyFlat.of_linearEquiv _ _ elin
  have hff : Module.FaithfullyFlat (Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭)) W :=
    Module.FaithfullyFlat.trans _ (Localization.AtPrime 𝔭) W
  exact ⟨algX, algP, tXP, tSX, hff, rfl⟩

end SMK26WR

namespace RAS26

open GoodReductionJacobian.RelativeGroupLaw

section Generic

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

abbrev bc (f : A ⟶ Spec (CommRingCat.of S)) (X : Type) [CommRing X] [Algebra S X] : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X)))
abbrev bcStr (f : A ⟶ Spec (CommRingCat.of S)) (X : Type) [CommRing X] [Algebra S X] :
    bc f X ⟶ Spec (CommRingCat.of X) :=
  pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))
abbrev bcFst (f : A ⟶ Spec (CommRingCat.of S)) (X : Type) [CommRing X] [Algebra S X] : bc f X ⟶ A :=
  pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X)))

def Compat {X : Type} [CommRing X] {AX : Scheme.{0}} (pX : AX ⟶ Spec (CommRingCat.of X))
    (jX : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of S)) (aX : AX ⟶ A) (haX : aX ≫ f = pX ≫ jX)
    (LX : RelativeGroupLaw X pX) : Prop :=
  ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of X)) (P Q : SchemeHomOver t' pX),
    (LX.mul t' P Q).1 ≫ aX =
      (L.mul (t' ≫ jX) ⟨P.1 ≫ aX, by rw [Category.assoc, haX, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ aX, by rw [Category.assoc, haX, ← Category.assoc, Q.2]⟩).1

theorem compat_baseChange {X : Type} [CommRing X] (jX : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of S)) :
    Compat L (pullback.snd f jX) jX (pullback.fst f jX) pullback.condition (L.baseChange jX) := by
  intro T t' P Q
  exact congrArg Subtype.val (baseChangePointToBase_mul jX L t' P Q)

theorem mul_coe_congr {R : Type} [CommRing R] {B : Scheme.{0}} {q : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R q)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (P₁ Q₁ : SchemeHomOver t₁ q) (P₂ Q₂ : SchemeHomOver t₂ q)
    (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (G.mul t₁ P₁ Q₁).1 = (G.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

theorem compat_congr {X : Type} [CommRing X] {AX : Scheme.{0}} (pX : AX ⟶ Spec (CommRingCat.of X))
    {jX jX' : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of S)} (hj : jX = jX') (aX : AX ⟶ A) (haX : aX ≫ f = pX ≫ jX)
    (LX : RelativeGroupLaw X pX) (h : Compat L pX jX aX haX LX) : Compat L pX jX' aX (hj ▸ haX) LX := by
  subst hj
  exact h

theorem compat_of_compat {X Y : Type} [CommRing X] [CommRing Y]
    {AX AY : Scheme.{0}} {pX : AX ⟶ Spec (CommRingCat.of X)} {pY : AY ⟶ Spec (CommRingCat.of Y)}
    {jX : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of S)} {jY : Spec (CommRingCat.of Y) ⟶ Spec (CommRingCat.of S)}
    {aX : AX ⟶ A} {aY : AY ⟶ A} (haX : aX ≫ f = pX ≫ jX) (hY : IsPullback aY pY f jY)
    (LX : RelativeGroupLaw X pX) (LY : RelativeGroupLaw Y pY)
    (hLX : Compat L pX jX aX haX LX) (hLY : Compat L pY jY aY hY.w LY)
    (ψ : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of Y)) (hψ : ψ ≫ jY = jX)
    (g : AX ⟶ AY) (hg₁ : g ≫ aY = aX) (hg₂ : g ≫ pY = pX ≫ ψ)
    (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of X)) (P Q : SchemeHomOver t' pX) :
    (LX.mul t' P Q).1 ≫ g =
      (LY.mul (t' ≫ ψ) ⟨P.1 ≫ g, by rw [Category.assoc, hg₂, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg₂, ← Category.assoc, Q.2]⟩).1 := by
  apply hY.hom_ext
  · rw [Category.assoc, hg₁, hLX T t' P Q, hLY T (t' ≫ ψ)]
    exact mul_coe_congr L (by rw [Category.assoc, hψ]) _ _ _ _ (by simp only [Category.assoc, hg₁])
      (by simp only [Category.assoc, hg₁])
  · rw [(LY.mul (t' ≫ ψ) _ _).2, Category.assoc, hg₂, ← Category.assoc, (LX.mul t' P Q).2]

theorem compat_comp {X Y : Type} [CommRing X] [CommRing Y]
    {AX : Scheme.{0}} {pX : AX ⟶ Spec (CommRingCat.of X)} {jX : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of S)}
    {aX : AX ⟶ A} (haX : aX ≫ f = pX ≫ jX) (LX : RelativeGroupLaw X pX) (hLX : Compat L pX jX aX haX LX)
    {AY : Scheme.{0}} {pY : AY ⟶ Spec (CommRingCat.of Y)} {jY : Spec (CommRingCat.of Y) ⟶ Spec (CommRingCat.of X)}
    {aY : AY ⟶ AX} (haY : aY ≫ pX = pY ≫ jY) (LY : RelativeGroupLaw Y pY) (hLY : Compat LX pY jY aY haY LY) :
    Compat L pY (jY ≫ jX) (aY ≫ aX) (by rw [Category.assoc, haX, ← Category.assoc, haY, Category.assoc]) LY := by
  intro T t' P Q
  rw [← Category.assoc, hLY T t' P Q, hLX T (t' ≫ jY)]
  exact mul_coe_congr L (Category.assoc _ _ _).symm _ _ _ _ (Category.assoc _ _ _) (Category.assoc _ _ _)

theorem specMap_algebraMap_comp {X Y : Type} [CommRing X] [CommRing Y] [Algebra S X] [Algebra S Y] [Algebra X Y]
    [IsScalarTower S X Y] :
    Spec.map (CommRingCat.ofHom (algebraMap X Y)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)) =
      Spec.map (CommRingCat.ofHom (algebraMap S Y)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

theorem isPullback_flatten (f : A ⟶ Spec (CommRingCat.of S)) (X T : Type) [CommRing X] [CommRing T] [Algebra S X] [Algebra S T]
    [Algebra X T] [IsScalarTower S X T] :
    IsPullback (pullback.fst (bcStr f X) (Spec.map (CommRingCat.ofHom (algebraMap X T))) ≫ bcFst f X)
      (pullback.snd (bcStr f X) (Spec.map (CommRingCat.ofHom (algebraMap X T)))) f
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
  have h := IsPullback.paste_horiz
    (IsPullback.of_hasPullback (bcStr f X) (Spec.map (CommRingCat.ofHom (algebraMap X T))))
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
  rwa [specMap_algebraMap_comp] at h

theorem exists_pinned (f : A ⟶ Spec (CommRingCat.of S)) {X Y : Type} [CommRing X] [CommRing Y] [Algebra S X] [Algebra S Y]
    (ψ : X →+* Y) (hψ : ψ.comp (algebraMap S X) = algebraMap S Y) :
    ∃ ρ : bc f Y ⟶ bc f X, ρ ≫ bcFst f X = bcFst f Y ∧ ρ ≫ bcStr f X = bcStr f Y ≫ Spec.map (CommRingCat.ofHom ψ) :=
  ⟨pullback.lift (bcFst f Y) (bcStr f Y ≫ Spec.map (CommRingCat.ofHom ψ))
      (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isPullback_of_proj (f : A ⟶ Spec (CommRingCat.of S)) {X Y : Type} [CommRing X] [CommRing Y]
    [Algebra S X] [Algebra S Y] (ψ : X →+* Y) (hψ : ψ.comp (algebraMap S X) = algebraMap S Y)
    (φ : bc f Y ⟶ bc f X) (hφ₁ : φ ≫ bcFst f X = bcFst f Y) (hφ₂ : φ ≫ bcStr f X = bcStr f Y ≫ Spec.map (CommRingCat.ofHom ψ)) :
    IsPullback φ (bcStr f Y) (bcStr f X) (Spec.map (CommRingCat.ofHom ψ)) := by
  refine IsPullback.of_right ?_ hφ₂ (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
  rw [hφ₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
  exact IsPullback.of_hasPullback f _

theorem specMap_id (W : Type) [CommRing W] : Spec.map (CommRingCat.ofHom (RingHom.id W)) = 𝟙 _ := by
  rw [CommRingCat.ofHom_id]; exact Spec.map_id _

theorem locIsoOnBase_of_iso {R : Type} [CommRing R] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩

end Generic

theorem root_transport {W : Type} [CommRing W] {B B' : Scheme.{0}} {g : B ⟶ Spec (CommRingCat.of W)}
    {g' : B' ⟶ Spec (CommRingCat.of W)} {θ : B ⟶ B'}
    (hθ : IsPullback θ g g' (Spec.map (CommRingCat.ofHom (RingHom.id W))))
    (Lg : RelativeGroupLaw W g) (Lg' : RelativeGroupLaw W g')
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of W)) (P Q : SchemeHomOver t' g),
      (Lg.mul t' P Q).1 ≫ θ =
        (Lg'.mul (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id W)))
          ⟨P.1 ≫ θ, by rw [Category.assoc, hθ.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ θ, by rw [Category.assoc, hθ.w, ← Category.assoc, Q.2]⟩).1)
    (N : B.Modules) (N' : B'.Modules) (eN : (Scheme.Modules.pullback θ).obj N' ≅ N)
    (𝓛₀' : B'.Modules) (h1 : Scheme.Modules.IsInvertible 𝓛₀') (h2 : KernelTrivial g' Lg' 𝓛₀') (h3 : IsSymmetric g' Lg' 𝓛₀')
    (h4 : LocIsoOnBase g' N' (𝓛₀' ⊗ (Scheme.Modules.pullback (negMor g' Lg')).obj 𝓛₀')) :
    ∃ 𝓛₀ : B.Modules, Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial g Lg 𝓛₀ ∧ IsSymmetric g Lg 𝓛₀ ∧
      LocIsoOnBase g N (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor g Lg)).obj 𝓛₀) := by
  refine ⟨(Scheme.Modules.pullback θ).obj 𝓛₀', h1.pullback θ,
    AlgebraicGeometry.Polarisation.KernelTrivial.pullback_of_isPullback (RingHom.id W) hθ Lg' Lg hmul 𝓛₀' h1 h2,
    AlgebraicGeometry.Polarisation.IsSymmetric.pullback_of_isPullback (RingHom.id W) hθ Lg' Lg hmul 𝓛₀' h3, ?_⟩
  have H := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_isPullback (RingHom.id W) hθ h4
  have E := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence g
  exact E.trans (locIsoOnBase_of_iso g eN.symm) (E.trans H (locIsoOnBase_of_iso g (NEG22.pullbackSqIso (RingHom.id W) hθ Lg' Lg hmul 𝓛₀')))

theorem rebase_of_ringEquiv {R R' C : Type} [CommRing R] [CommRing R'] [CommRing C] (e : R ≃+* R') [Algebra R' C]
    (hfin : Module.Finite R' C) (hff : Module.FaithfullyFlat R' C) (hfp : Algebra.FinitePresentation R' C) :
    letI : Algebra R C := ((algebraMap R' C).comp e.toRingHom).toAlgebra
    Module.Finite R C ∧ Module.FaithfullyFlat R C ∧ Algebra.FinitePresentation R C := by
  letI algRC : Algebra R C := ((algebraMap R' C).comp e.toRingHom).toAlgebra
  letI algRR' : Algebra R R' := e.toRingHom.toAlgebra
  haveI : IsScalarTower R R' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := hfin; haveI := hff; haveI := hfp
  have elin : R ≃ₗ[R] R' :=
    { e.toAddEquiv with
      map_smul' := fun c x => by
        show e (c * x) = e c * e x
        exact map_mul e c x }
  have ealg : R ≃ₐ[R] R' := AlgEquiv.ofRingEquiv (f := e) (fun x => rfl)
  haveI : Module.Finite R R' := Module.Finite.equiv elin
  haveI : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_linearEquiv _ _ elin.symm
  haveI : Algebra.FinitePresentation R R' := Algebra.FinitePresentation.equiv ealg
  exact ⟨Module.Finite.trans R' C, Module.FaithfullyFlat.trans R R' C, Algebra.FinitePresentation.trans R R' C⟩

theorem exists_numerator {S : Type} [CommRing S] (𝔭 : Ideal S) [h𝔭 : 𝔭.IsPrime] (g₀ : S) (hg₀ : g₀ ∉ 𝔭)
    (gL : Localization.Away g₀) (hgL : gL ∉ Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭) :
    ∃ s : S, s ∉ 𝔭 ∧ IsLocalization.Away (g₀ * s) (Localization.Away gL) := by
  classical
  have h𝔭X := SMK26WR.isPrime_map_away 𝔭 g₀ hg₀
  obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hs⟩ := IsLocalization.surj (Submonoid.powers g₀) gL
  refine ⟨s, ?_, ?_⟩
  · intro hs𝔭
    apply hgL
    have h1 : gL * algebraMap S (Localization.Away g₀) (g₀ ^ n) ∈ Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭 := by
      rw [show gL * algebraMap S (Localization.Away g₀) (g₀ ^ n) = algebraMap S (Localization.Away g₀) s from hs]
      exact Ideal.mem_map_of_mem _ hs𝔭
    rcases h𝔭X.mem_or_mem h1 with h | h
    · exact h
    · exfalso
      have h' : g₀ ^ n ∈ (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭).comap (algebraMap S (Localization.Away g₀)) := h
      rw [SMK26WR.comap_map_away 𝔭 g₀ hg₀] at h'
      exact hg₀ (h𝔭.mem_of_pow_mem n h')
  · have hu : IsUnit (algebraMap S (Localization.Away g₀) (g₀ ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit g₀).pow n
    obtain ⟨u, hu'⟩ := hu
    have hassoc : Associated (algebraMap S (Localization.Away g₀) s) gL := by
      refine ⟨u⁻¹, ?_⟩
      rw [← hs, ← hu', _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    exact IsLocalization.Away.mul_of_associated g₀ s gL (T := Localization.Away gL) hassoc

section Stage

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem stageRoot (g₀ : S)
    (𝓜 : (bc f (Localization.Away g₀)).Modules)
    (W : Type) [CommRing W] [Algebra S W] [Algebra (Localization.Away g₀) W] [IsScalarTower S (Localization.Away g₀) W]
    (κ : bc f W ⟶ bc f (Localization.Away g₀))
    (hκ₁ : κ ≫ bcFst f (Localization.Away g₀) = bcFst f W)
    (hκ₂ : κ ≫ bcStr f (Localization.Away g₀) = bcStr f W ≫ Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W)))
    (hroot : ∀ (L' : RelativeGroupLaw W (bcStr f W)),
      Compat L (bcStr f W) (Spec.map (CommRingCat.ofHom (algebraMap S W))) (bcFst f W) pullback.condition L' →
      ∃ 𝓛₀ : (bc f W).Modules,
        Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (bcStr f W) L' 𝓛₀ ∧ IsSymmetric (bcStr f W) L' 𝓛₀ ∧
        LocIsoOnBase (bcStr f W) ((Scheme.Modules.pullback κ).obj 𝓜) (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (bcStr f W) L')).obj 𝓛₀))
    (L' : RelativeGroupLaw W (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W)))))
    (hL' : Compat (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
      (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W))))
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W)))
      (pullback.fst (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W))))
      pullback.condition L') :
    ∃ 𝓛₀ : (pullback (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W)))).Modules,
      Scheme.Modules.IsInvertible 𝓛₀ ∧
      KernelTrivial (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W)))) L' 𝓛₀ ∧
      IsSymmetric (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W)))) L' 𝓛₀ ∧
      LocIsoOnBase (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W))))
        ((Scheme.Modules.pullback (pullback.fst (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W))))).obj 𝓜)
        (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W)))) L')).obj 𝓛₀) := by
  classical
  have hflat := isPullback_flatten f (Localization.Away g₀) W

  obtain ⟨θ, hθ1, hθ2⟩ : ∃ θ : pullback (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W))) ⟶ bc f W,
      θ ≫ bcFst f W = pullback.fst _ _ ≫ bcFst f (Localization.Away g₀) ∧ θ ≫ bcStr f W = pullback.snd _ _ :=
    ⟨pullback.lift (pullback.fst _ _ ≫ bcFst f (Localization.Away g₀)) (pullback.snd _ _) hflat.w,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  obtain ⟨LW, hLW⟩ : ∃ LW : RelativeGroupLaw W (bcStr f W),
      Compat L (bcStr f W) (Spec.map (CommRingCat.ofHom (algebraMap S W))) (bcFst f W) pullback.condition LW :=
    ⟨_, compat_baseChange L _⟩
  obtain ⟨𝓛₀'', h1, h2, h3, h4⟩ := hroot LW hLW

  have hθ : IsPullback θ
      (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W))))
      (bcStr f W) (Spec.map (CommRingCat.ofHom (RingHom.id W))) := by
    rw [specMap_id]
    refine IsPullback.of_right ?_ (by rw [hθ2, Category.comp_id])
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
    rw [hθ1, Category.id_comp]
    exact hflat

  have hL'S := compat_comp L pullback.condition _ (compat_baseChange L (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))) pullback.condition L' hL'
  have hmul := compat_of_compat L (X := W) (Y := W) _ (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
    L' LW hL'S hLW
    (Spec.map (CommRingCat.ofHom (RingHom.id W))) (by rw [specMap_id, Category.id_comp, specMap_algebraMap_comp])
    θ hθ1 (by rw [hθ2, specMap_id, Category.comp_id])

  have hθκ : θ ≫ κ =
      pullback.fst (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) W))) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hκ₁, hθ1]
    · rw [Category.assoc, hκ₂, ← Category.assoc, hθ2, pullback.condition]
  exact root_transport hθ L' _ (fun t' P Q => hmul _ t' P Q) _ _
    ((Scheme.Modules.pullbackComp _ _).app 𝓜 ≪≫ (Scheme.Modules.pullbackCongr hθκ).app 𝓜) 𝓛₀'' h1 h2 h3 h4

theorem finalRoot (g₀ : S)
    (𝓜 : (bc f (Localization.Away g₀)).Modules)
    (C : Type) [CommRing C] [Algebra S C] [Algebra (Localization.Away g₀) C] [IsScalarTower S (Localization.Away g₀) C]
    (π : bc f C ⟶ bc f (Localization.Away g₀))
    (hπ₁ : π ≫ bcFst f (Localization.Away g₀) = bcFst f C)
    (hπ₂ : π ≫ bcStr f (Localization.Away g₀) = bcStr f C ≫ Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C)))
    (hrootC : ∀ (L' : RelativeGroupLaw C (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C))))),
      Compat (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
        (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C))))
        (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C)))
        (pullback.fst (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C))))
        pullback.condition L' →
      ∃ 𝓛₀ : (pullback (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C)))).Modules,
        Scheme.Modules.IsInvertible 𝓛₀ ∧
        KernelTrivial (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C)))) L' 𝓛₀ ∧
        IsSymmetric (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C)))) L' 𝓛₀ ∧
        LocIsoOnBase (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C))))
          ((Scheme.Modules.pullback (pullback.fst (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C))))).obj 𝓜)
          (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C)))) L')).obj 𝓛₀))
    (L' : RelativeGroupLaw C (bcStr f C))
    (hL' : Compat L (bcStr f C) (Spec.map (CommRingCat.ofHom (algebraMap S C))) (bcFst f C) pullback.condition L') :
    ∃ 𝓛₀ : (bc f C).Modules,
      Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (bcStr f C) L' 𝓛₀ ∧ IsSymmetric (bcStr f C) L' 𝓛₀ ∧
      LocIsoOnBase (bcStr f C) ((Scheme.Modules.pullback π).obj 𝓜) (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (bcStr f C) L')).obj 𝓛₀) := by
  classical
  have hflat := isPullback_flatten f (Localization.Away g₀) C
  have hπ : IsPullback π (bcStr f C) (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C))) :=
    isPullback_of_proj f (algebraMap (Localization.Away g₀) C) (IsScalarTower.algebraMap_eq S (Localization.Away g₀) C).symm π hπ₁ hπ₂

  obtain ⟨μ, hμ1, hμ2⟩ : ∃ μ : bc f C ⟶ pullback (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C))),
      μ ≫ pullback.fst _ _ = π ∧ μ ≫ pullback.snd _ _ = bcStr f C :=
    ⟨pullback.lift π (bcStr f C) hπ₂, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  obtain ⟨LW, hLW⟩ : ∃ LW : RelativeGroupLaw C (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C)))),
      Compat (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
        (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C))))
        (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C)))
        (pullback.fst (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C))))
        pullback.condition LW :=
    ⟨_, compat_baseChange _ _⟩
  obtain ⟨𝓛₀'', h1, h2, h3, h4⟩ := hrootC LW hLW

  have hθ : IsPullback μ (bcStr f C)
      (pullback.snd (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C))))
      (Spec.map (CommRingCat.ofHom (RingHom.id C))) := by
    rw [specMap_id]
    refine IsPullback.of_right ?_ (by rw [hμ2, Category.comp_id])
      (IsPullback.of_hasPullback (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C))))
    rw [hμ1, Category.id_comp]
    exact hπ

  have hWS := compat_comp L pullback.condition _ (compat_baseChange L (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))) pullback.condition
    LW hLW
  have hmul := compat_of_compat L (X := C) (Y := C) pullback.condition
    ((IsPullback.of_hasPullback (bcStr f (Localization.Away g₀)) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) C)))).paste_horiz
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))))
    L' LW hL' hWS
    (Spec.map (CommRingCat.ofHom (RingHom.id C))) (by rw [specMap_id, Category.id_comp, specMap_algebraMap_comp])
    μ (by rw [← Category.assoc, hμ1, hπ₁]) (by rw [hμ2, specMap_id, Category.comp_id])
  exact root_transport hθ L' _ (fun t' P Q => hmul _ t' P Q) _ _
    ((Scheme.Modules.pullbackComp _ _).app 𝓜 ≪≫ (Scheme.Modules.pullbackCongr hμ1).app 𝓜) 𝓛₀'' h1 h2 h3 h4

end Stage

end RAS26

open RAS26 in
theorem solution
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (hLRC : (∀ {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (𝔭 : PrimeSpectrum S)
    (W : Type) [CommRing W] [Algebra S W] [Algebra (Localization.AtPrime 𝔭.asIdeal) W]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) W] (hW : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W)
    (hroot : (∀ (L' : RelativeGroupLaw W (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of W))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S W)))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
            IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))))).obj 𝓛)
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L')).obj 𝓛₀))),
      ∃ (g : S) (_ : g ∉ 𝔭.asIdeal) (C : Type) (_ : CommRing C) (_ : Algebra S C) (_ : Algebra (Localization.Away g) C)
      (_ : IsScalarTower S (Localization.Away g) C),
      Module.Finite (Localization.Away g) C ∧ Module.FaithfullyFlat (Localization.Away g) C ∧
      Algebra.FinitePresentation (Localization.Away g) C ∧
      (∀ (L' : RelativeGroupLaw C (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C)))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L' 𝓛₀ ∧
            IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))))).obj 𝓛)
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L')).obj 𝓛₀))))
    (𝔭 : PrimeSpectrum S)
    (g₀ : S) (hg₀ : g₀ ∉ 𝔭.asIdeal)
    (𝓜 : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))).Modules)
    (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (W : Type) [CommRing W] [Algebra S W] [Algebra (Localization.AtPrime 𝔭.asIdeal) W] [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) W]
    (hW : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W)
    (φW : (Localization.Away g₀) →+* W) (hφW : φW.comp (algebraMap S (Localization.Away g₀)) = algebraMap S W)
    (κ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
    (hκ₁ : κ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
    (hκ₂ : κ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ≫ Spec.map (CommRingCat.ofHom φW))
    (hroot : ∀ (L' : RelativeGroupLaw W (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of W))
            (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S W))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
      ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules,
        Scheme.Modules.IsInvertible 𝓛₀ ∧
        KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
        IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
        LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
          ((Scheme.Modules.pullback κ).obj 𝓜)
          (𝓛₀ ⊗ (Scheme.Modules.pullback
            (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L')).obj 𝓛₀)) :
    ∃ (s : S) (_ : s ∉ 𝔭.asIdeal) (C : Type) (_ : CommRing C) (_ : Algebra S C) (_ : Algebra (Localization.Away (g₀ * s)) C)
      (_ : IsScalarTower S (Localization.Away (g₀ * s)) C)
      (φ : (Localization.Away g₀) →+* C) (_ : φ.comp (algebraMap S (Localization.Away g₀)) = algebraMap S C)
      (π : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
      (_ : π ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))))
      (_ : π ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))) ≫ Spec.map (CommRingCat.ofHom φ)),
      Module.Finite (Localization.Away (g₀ * s)) C ∧ Module.FaithfullyFlat (Localization.Away (g₀ * s)) C ∧
      Algebra.FinitePresentation (Localization.Away (g₀ * s)) C ∧
      ∀ (L' : RelativeGroupLaw C (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C))
            (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S C))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C)))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧
          KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L' 𝓛₀ ∧
          IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L' 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))
            ((Scheme.Modules.pullback π).obj 𝓜)
            (𝓛₀ ⊗ (Scheme.Modules.pullback
              (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L')).obj 𝓛₀) := by
  classical
  haveI : IsNoetherianRing (Localization.Away g₀) :=
    IsLocalization.isNoetherianRing (Submonoid.powers g₀) _ inferInstance
  have h𝔭X : (Ideal.map (algebraMap S (Localization.Away g₀)) 𝔭.asIdeal).IsPrime := SMK26WR.isPrime_map_away 𝔭.asIdeal g₀ hg₀

  have hu₀ : IsUnit (algebraMap S (Localization.AtPrime 𝔭.asIdeal) g₀) :=
    IsLocalization.map_units (Localization.AtPrime 𝔭.asIdeal) (⟨g₀, hg₀⟩ : 𝔭.asIdeal.primeCompl)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Localization.Away g₀ →+* Localization.AtPrime 𝔭.asIdeal,
      ψ.comp (algebraMap S (Localization.Away g₀)) = algebraMap S (Localization.AtPrime 𝔭.asIdeal) :=
    ⟨IsLocalization.Away.lift g₀ hu₀, IsLocalization.Away.lift_comp g₀ hu₀⟩

  obtain ⟨algXW, algPW, tXPW, tSXW, hWff, -⟩ :=
    SMK26WR.exists_algebra_atPrime_map_faithfullyFlat 𝔭.asIdeal g₀ hg₀ ψ hψ W hW
  letI := algXW
  letI := algPW
  haveI := tXPW
  haveI := tSXW
  have hφW' : φW = algebraMap (Localization.Away g₀) W := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g₀)
    rw [hφW, ← IsScalarTower.algebraMap_eq]

  have hAX : AbelianSchemePropertyBundle (Localization.Away g₀) (bcStr f (Localization.Away g₀)) :=
    hA.of_isPullback (IsPullback.of_hasPullback f _)

  have hrootX := stageRoot L g₀ 𝓜 W κ hκ₁ (by rw [hκ₂, hφW']) (fun L' hL' => hroot L' hL')

  obtain ⟨gL, hgL, C, instC, algXC, algLC, tXLC, hfin, hff, hfp, hrootC⟩ :=
    hLRC (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))) hAX 𝓜 h𝓜
      ⟨_, h𝔭X⟩ W hWff (fun L' hL' => hrootX L' hL')
  letI := instC
  letI := algXC
  letI := algLC
  haveI := tXLC

  obtain ⟨s, hs𝔭, hAw⟩ := exists_numerator 𝔭.asIdeal g₀ hg₀ gL hgL
  haveI := hAw
  obtain ⟨e⟩ : Nonempty (Localization.Away (g₀ * s) ≃ₐ[S] Localization.Away gL) :=
    ⟨IsLocalization.algEquiv (Submonoid.powers (g₀ * s)) _ _⟩

  letI algSC : Algebra S C := ((algebraMap (Localization.Away g₀) C).comp (algebraMap S (Localization.Away g₀))).toAlgebra
  haveI tSXC : IsScalarTower S (Localization.Away g₀) C :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := Localization.Away g₀) (A := C) (fun _ => rfl)
  obtain ⟨hfin', hff', hfp'⟩ := rebase_of_ringEquiv (C := C) e.toRingEquiv hfin hff hfp
  letI algGC : Algebra (Localization.Away (g₀ * s)) C :=
    ((algebraMap (Localization.Away gL) C).comp e.toRingEquiv.toRingHom).toAlgebra
  haveI tSGC : IsScalarTower S (Localization.Away (g₀ * s)) C :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := Localization.Away (g₀ * s)) (A := C) (fun x => by
      change algebraMap (Localization.Away g₀) C (algebraMap S (Localization.Away g₀) x) =
        algebraMap (Localization.Away gL) C (e (algebraMap S (Localization.Away (g₀ * s)) x))
      rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply S (Localization.Away g₀) (Localization.Away gL) x,
        ← IsScalarTower.algebraMap_apply (Localization.Away g₀) (Localization.Away gL) C])

  obtain ⟨π, hπ₁, hπ₂⟩ := exists_pinned f (X := Localization.Away g₀) (Y := C) (algebraMap (Localization.Away g₀) C) rfl
  refine ⟨s, hs𝔭, C, instC, algSC, algGC, tSGC, algebraMap (Localization.Away g₀) C, rfl, π, hπ₁, hπ₂, hfin', hff', hfp', ?_⟩
  intro L' hL'
  exact finalRoot L g₀ 𝓜 C π hπ₁ hπ₂ (fun LW hLW => hrootC LW hLW) L' hL'

end
end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_away_mul_of_symmetric_principalSqrt_faithfullyFlat_atPrime
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_away_mul_of_symmetric_principalSqrt_faithfullyFlat_atPrime (solution)
