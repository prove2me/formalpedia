-- Prove2me | solution 1 for GoodReductionJacobian.abelianSchemePropertyBundle_pullback_snd_ratLocalizedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/90cb649f-a01d-5e55-a993-e58ecdfb84e5

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_abelianSchemePropertyBundle_pullback_snd_ratLocalizedAt

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_abelianSchemePropertyBundle_pullback_snd_ratLocalizedAt.GoodReductionJacobian"

universe u

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle RelativeGroupLaw"
namespace C2Core
p2m_open "GoodReductionJacobian"

section FibreTransfer

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (ι : Y' ⟶ Y) (s : Y')

theorem isIso_residueFieldMap_of_surjectiveOnStalks [SurjectiveOnStalks ι] :
    IsIso (ι.residueFieldMap s) := by
  have hsurj : Function.Surjective (ι.residueFieldMap s).hom := by
    have h2 : Function.Surjective (ι.stalkMap s ≫ Y'.residue s).hom := by
      rw [CommRingCat.hom_comp, RingHom.coe_comp]
      exact (Y'.residue_surjective s).comp (SurjectiveOnStalks.stalkMap_surjective ι s)
    rw [← Scheme.residue_residueFieldMap, CommRingCat.hom_comp, RingHom.coe_comp] at h2
    exact Function.Surjective.of_comp h2
  have hbij : Function.Bijective (ι.residueFieldMap s).hom :=
    ⟨(ι.residueFieldMap s).hom.injective, hsurj⟩
  have : IsIso ((forget CommRingCat).map (ι.residueFieldMap s)) :=
    (isIso_iff_bijective ((forget CommRingCat).map (ι.residueFieldMap s))).mpr hbij
  exact isIso_of_reflects_iso (ι.residueFieldMap s) (forget CommRingCat)

noncomputable def fiberSndIso [IsIso (ι.residueFieldMap s)] :
    (pullback.snd f ι).fiber s ≅ f.fiber (ι.base s) :=
  pullbackLeftPullbackSndIso f ι (Y'.fromSpecResidueField s) ≪≫
    pullback.congrHom rfl (ι.SpecMap_residueFieldMap_fromSpecResidueField s).symm ≪≫
    (pullbackLeftPullbackSndIso f (Y.fromSpecResidueField (ι.base s))
      (Spec.map (ι.residueFieldMap s))).symm ≪≫
    @asIso _ _ _ _ (pullback.fst (pullback.snd f (Y.fromSpecResidueField (ι.base s)))
      (Spec.map (ι.residueFieldMap s))) (pullback_fst_iso_of_right_iso _ _)

noncomputable def preimageSndHomeo [IsIso (ι.residueFieldMap s)] :
    ↥((pullback.snd f ι).base ⁻¹' {s}) ≃ₜ ↥(f.base ⁻¹' {ι.base s}) :=
  ((pullback.snd f ι).fiberHomeo s).symm.trans
    ((Scheme.homeoOfIso (fiberSndIso f ι s)).trans (f.fiberHomeo (ι.base s)))

theorem isPreconnected_preimage_snd [IsIso (ι.residueFieldMap s)]
    (h : _root_.IsPreconnected (f.base ⁻¹' {ι.base s})) :
    _root_.IsPreconnected ((pullback.snd f ι).base ⁻¹' {s}) := by
  haveI : PreconnectedSpace ↥(f.base ⁻¹' {ι.base s}) := Subtype.preconnectedSpace h
  have hr := isPreconnected_range (preimageSndHomeo f ι s).symm.continuous
  rw [Homeomorph.range_coe] at hr
  exact isPreconnected_iff_preconnectedSpace.mpr ⟨hr⟩

end FibreTransfer

section Proper

theorem isProper_pullback_snd_comp {X S S' S'' : Scheme.{u}} (f : X ⟶ S) (a : S' ⟶ S) (b : S'' ⟶ S')
    [IsProper (pullback.snd f a)] : IsProper (pullback.snd f (b ≫ a)) := by
  have e : pullback.snd f (b ≫ a) =
      (pullbackLeftPullbackSndIso f a b).inv ≫ pullback.snd (pullback.snd f a) b := by
    rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]
  rw [e]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mpr inferInstance

end Proper

section RatLocalizedAt

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem surjectiveOnStalks_specMap_ratLocalizedAt :
    SurjectiveOnStalks (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) := by
  haveI : (Ideal.span {(ℓ : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hℓ.out.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hℓ.out)
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := ℓ) hℓ.out
  exact SurjectiveOnStalks.Spec_iff.mpr
    (RingHom.surjectiveOnStalks_of_isLocalization (Ideal.span {(ℓ : ℤ)}).primeCompl
      ↥(GaloisRep.ratLocalizedAt ℓ))

theorem isUnit_algebraMap_ratLocalizedAt {p : ℕ} (hℓp : ¬ ℓ ∣ p) :
    IsUnit (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ) p) := by
  have hp0 : p ≠ 0 := by rintro rfl; exact hℓp (dvd_zero ℓ)
  have hmem : ((p : ℚ))⁻¹ ∈ GaloisRep.ratLocalizedAt ℓ := by
    show ((p : ℚ)⁻¹).den.Coprime ℓ
    rw [Rat.inv_natCast_den_of_pos (Nat.pos_of_ne_zero hp0)]
    exact ((Nat.Prime.coprime_iff_not_dvd hℓ.out).mpr hℓp).symm
  rw [map_natCast]
  refine isUnit_iff_exists_inv.mpr ⟨⟨(p : ℚ)⁻¹, hmem⟩, Subtype.ext ?_⟩
  simp [hp0]

theorem exists_specMap_ratLocalizedAt_eq_comp {p : ℕ} (hℓp : ¬ ℓ ∣ p) :
    ∃ φ : Localization.Away (p : ℤ) →+* ↥(GaloisRep.ratLocalizedAt ℓ),
      Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))) =
        Spec.map (CommRingCat.ofHom φ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))) := by
  refine ⟨IsLocalization.Away.lift (p : ℤ) (isUnit_algebraMap_ratLocalizedAt ℓ hℓp), ?_⟩
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.Away.lift_comp]

end RatLocalizedAt

end GoodReductionJacobian.C2Core

open GoodReductionJacobian.C2Core in

theorem solution
    (p ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [Smooth g] (L : RelativeGroupLaw ℤ g)
    (hconn : ∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (g.base ⁻¹' {s}))
    (hprop : IsProper (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))))))
    : AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ)
        (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))) := by
  refine ⟨inferInstance, ?_, ?_, ⟨L.baseChange _⟩⟩
  ·
    obtain ⟨φ, hφ⟩ := exists_specMap_ratLocalizedAt_eq_comp ℓ hℓp
    rw [hφ]
    haveI := hprop
    exact isProper_pullback_snd_comp g _ _
  · intro s
    refine ⟨?_, ?_⟩
    ·
      have h1 := (L.one (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))).2
      let σ : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)) ⟶
          pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) :=
        pullback.lift (L.one _).1 (𝟙 _) (by rw [h1, Category.id_comp])
      have hσ : σ ≫ pullback.snd g _ = 𝟙 _ := pullback.lift_snd _ _ _
      refine ⟨σ.base s, ?_⟩
      simpa using congrArg (fun k => k.base s) hσ
    ·
      haveI := surjectiveOnStalks_specMap_ratLocalizedAt ℓ
      haveI := isIso_residueFieldMap_of_surjectiveOnStalks
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) s
      exact isPreconnected_preimage_snd g _ s (hconn _)

end S_GoodReductionJacobian_abelianSchemePropertyBundle_pullback_snd_ratLocalizedAt
end P2MW
export P2MW.S_GoodReductionJacobian_abelianSchemePropertyBundle_pullback_snd_ratLocalizedAt (solution)
