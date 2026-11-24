-- Prove2me | solution 1 for GlobalTheory.isIso_specMap_restrict_basicOpen_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:03:42.603177+00:00
-- url     : https://prove2.me/submissions/6f9cc1d0-7d1d-41c2-b2e0-01e82290220c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelSpecMapIsIsoOverBasicOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option autoImplicit false
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R S : CommRingCat.{0}} (f : R ⟶ S) (r : R)
    (h : Function.Bijective (Localization.awayMap f.hom r)) :
    IsIso (Spec.map f ∣_ (PrimeSpectrum.basicOpen r : (Spec R).Opens)) := by
  set φ := Spec.map f with hφ
  set g : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv r with hg
  have hbo : (PrimeSpectrum.basicOpen r : (Spec R).Opens) = (Spec R).basicOpen g :=
    (basicOpen_eq_of_affine (R := R) r).symm
  rw [hbo]
  have hU := isAffineOpen_top (Spec R)
  have hpre : IsAffineOpen (φ ⁻¹ᵁ (⊤ : (Spec R).Opens)) := by
    simpa using isAffineOpen_top (Spec S)
  have nat : ∀ x : R, (φ.app ⊤).hom ((Scheme.ΓSpecIso R).inv x) =
      (Scheme.ΓSpecIso S).inv (f x) := fun x =>
    (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality f)).symm
  have hi := (IsLocalization.Away.map_injective_iff (S := Localization.Away r)
    (Q := Localization.Away (f.hom r)) f.hom r).mp h.1
  have hs := (IsLocalization.Away.map_surjective_iff (S := Localization.Away r)
    (Q := Localization.Away (f.hom r)) f.hom r).mp h.2
  rw [isIso_morphismRestrict_iff_isIso_app _ (hU.basicOpen g),
    hU.app_basicOpen_eq_away_map φ hpre g]
  refine IsIso.comp_isIso' ?_ inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  have := hU.isLocalization_basicOpen g
  have := hpre.isLocalization_basicOpen ((φ.app ⊤).hom g)
  constructor
  · refine (IsLocalization.Away.map_injective_iff _ _ _).2 fun a ha => ?_
    obtain ⟨x, rfl⟩ : ∃ x, (Scheme.ΓSpecIso R).inv x = a :=
      ⟨(Scheme.ΓSpecIso R).hom a, Iso.hom_inv_id_apply _ _⟩
    rw [nat] at ha
    have hx : f x = 0 := by
      have := congrArg (Scheme.ΓSpecIso S).hom ha
      rw [Iso.inv_hom_id_apply] at this
      exact this.trans (map_zero _)
    obtain ⟨n, hn⟩ := hi x hx
    exact ⟨n, by rw [hg, ← map_pow, ← map_mul, hn, map_zero]⟩
  · refine (IsLocalization.Away.map_surjective_iff _ _ _ _).2 fun b => ?_
    obtain ⟨y, rfl⟩ : ∃ y, (Scheme.ΓSpecIso S).inv y = b :=
      ⟨(Scheme.ΓSpecIso S).hom b, Iso.hom_inv_id_apply _ _⟩
    obtain ⟨c, m, e⟩ := hs y
    exact ⟨(Scheme.ΓSpecIso R).inv c, m, by
      rw [nat, hg, nat]
      exact (congrArg (Scheme.ΓSpecIso S).inv.hom e).trans
        ((map_mul _ _ _).trans (congrArg (· * _) (map_pow _ _ _)))⟩
end GlobalTheory
